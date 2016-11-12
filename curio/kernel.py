# curio/kernel.py
#
# Main execution kernel.

import socket
import heapq
import time
import os
import sys
import logging
import signal
from selectors import DefaultSelector
from collections import deque, defaultdict, namedtuple

# Logger where uncaught exceptions from crashed tasks are logged
log = logging.getLogger(__name__)

from .errors import *
from .errors import _CancelRetry
from .task import Task
from .traps import _read_wait, Traps, SyncTraps
from .local import _enable_tasklocal_for, _copy_tasklocal

# kqueue is the datatype used by the kernel for all of its queuing functionality.
# Any time a task queue is needed, use this type instead of directly hard-coding the
# use of a deque.  This will make sure the code continues to work even if the
# queue type is changed later.

kqueue = deque

# ----------------------------------------------------------------------
# Wrapper around underlying selector API
# ----------------------------------------------------------------------

# There are two tricky issues with the stdlib 'selectors' API.
# First, it works with a mapping:
#
#   fileno -> (read/write bitmask, opaque data tag)
#
# where there can only be one entry per fileno. But we can have arbitrarily
# many different tasks interested in reading or writing to the same fileno,
# and these can come and go independently. So this class adds a facade that
# lets us register/unregister independent (fileno, event type, task)
# interests, and then compiles that down into the selectors representation.
#
# Second, registering and unregistering an interest can be rather slow, and
# it's rather common for a task to block repeatedly on the same interest. So
# as an optimization, we apply a "debouncing filter": we batch up changes
# waiting for select() to be called, and if we see a matching
# unregister/register pair with no select call in between, then we can skip
# them both. (XX FIXME: is this actually an optimization?)

Interest = namedtuple("Interest", ["fd", "event", "task"])

def _combined_flags(interests):
    flags = 0
    for interest in interests:
        flags |= interest.event
    return flags

def _fileno(fileobj):
    if isinstance(fileobj, int):
        return fileobj
    else:
        return fileobj.fileno()

class IOManager:
    def __init__(self, selector):
        self._selector = selector
        # In the vast vast majority of cases, there will only be 1 or 2
        # interests registered per fileno, so linear scans over interest sets
        # are going to beat fancier data structures. (I guess this could bite
        # you if you decide you want 1000 tasks all simultaneously
        # reading/writing to the same file descriptor, but... really?)
        self._fd_interests = {}
        # Stores the read/write flags that are currently registered in the
        # underlying selector, for fds that have been modified since the last
        # time we called select. These are the ones that might need to be
        # updated before we call select() again.
        self._fd_old_flags = {}

    def _get_interests_for_modification(self, fd):
        # We have to work with integer filenos, because otherwise we can get
        # aliasing between different file objects that have the same fileno
        # and then all kinds of nasty stuff could happen.
        assert isinstance(fd, int)
        interests = self._fd_interests.setdefault(fd, set())
        if fd not in self._fd_old_flags:
            self._fd_old_flags[fd] = _combined_flags(interests)
        return interests

    def register(self, fileobj, event, task):
        #print("register", fileobj, event, task)
        fd = _fileno(fileobj)
        interests = self._get_interests_for_modification(fd)
        interests.add(Interest(fd, event, task))

    def unregister(self, fileobj, event, task):
        #print("unregister", fileobj, event, task)
        fd = _fileno(fileobj)
        interests = self._get_interests_for_modification(fd)
        interests.remove(Interest(fd, event, task))
        # Don't worry about cleaning up newly-empty interest sets -- it makes
        # life easier to leave them alone for now, and handle them in select.

    def select(self, timeout):
        # print("entering select")
        # print("fd_old_flags", self._fd_old_flags)
        for fd, old_flags in self._fd_old_flags.items():
            interests = self._fd_interests[fd]
            if not interests:
                del self._fd_interests[fd]
            new_flags = _combined_flags(interests)
            #print("adjusting flags", fd, old_flags, new_flags)
            if old_flags != new_flags:
                if not new_flags:
                    self._selector.unregister(fd)
                elif not old_flags:
                    self._selector.register(fd, new_flags)
                else:
                    self._selector.modify(fd, new_flags)
        self._fd_old_flags.clear()
        for key, mask in self._selector.select(timeout):
            for interest in list(self._fd_interests[key.fd]):
                if interest.event & mask:
                    yield interest.task
                    self.unregister(*interest)

    def close(self):
        self._selector.close()

# ----------------------------------------------------------------------
# Underlying kernel that drives everything
# ----------------------------------------------------------------------

class Kernel(object):
    def __init__(self, *, selector=None, with_monitor=False, pdb=False, log_errors=True,
                 crash_handler=None):
        if selector is None:
            selector = DefaultSelector()

        self._iomanager = IOManager(selector)
        self._ready = kqueue()            # Tasks ready to run
        self._tasks = { }                 # Task table
        # Dict { signo: [ sigsets ] } of watched signals (initialized only if signals used)
        self._signal_sets = None
        self._default_signals = None      # Dict of default signal handlers

        # Attributes related to the loopback socket (only initialized if required)
        self._notify_sock = None
        self._wait_sock = None
        self._kernel_task_id = None

        # Wake queue for tasks restarted by external threads
        self._wake_queue = deque()

        # Sleeping task queue
        self._sleeping = []

        # Optional process/thread pools (see workers.py)
        self._thread_pool = None
        self._process_pool = None

        # Optional crash handler callback
        self._crash_handler = crash_handler

        self._pdb = pdb
        self._log_errors = log_errors

        # If a monitor is specified, launch it
        if with_monitor or 'CURIOMONITOR' in os.environ:
            Monitor(self)

    def __del__(self):
        if self._iomanager is not None:
            raise RuntimeError('Curio kernel not properly terminated.  Please use Kernel.run(shutdown=True)')

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.run(shutdown=True)

    # Force the kernel to wake, possibly scheduling a task to run.
    # This method is called by threads running concurrently to the
    # curio kernel.  For example, it's triggered upon completion of
    # Futures created by thread pools and processes. It's inherently
    # dangerous for any kind of operation on the kernel to be
    # performed by a separate thread.  Thus, the *only* thing that
    # happens here is that the task gets appended to a deque and a
    # notification message is written to the kernel notification
    # socket.  append() and pop() operations on deques are thread safe
    # and do not need additional locking.  See
    # https://docs.python.org/3/library/collections.html#collections.deque
    # ----------
    def _wake(self, task=None, future=None):
        if task:
            self._wake_queue.append((task, future))
        self._notify_sock.send(b'\x00')

    def _init_loopback(self):
        self._notify_sock, self._wait_sock = socket.socketpair()
        self._wait_sock.setblocking(False)
        self._notify_sock.setblocking(False)
        return self._wait_sock.fileno()

    def _init_signals(self):
        self._signal_sets = defaultdict(list)
        self._default_signals = { }
        old_fd = signal.set_wakeup_fd(self._notify_sock.fileno())
        assert old_fd < 0, 'Signals already initialized %d' % old_fd

    def _signal_watch(self, sigset):
        for signo in sigset.signos:
            if not self._signal_sets[signo]:
                self._default_signals[signo] = signal.signal(signo, lambda signo, frame: None)
            self._signal_sets[signo].append(sigset)

    def _signal_unwatch(self, sigset):
        for signo in sigset.signos:
            if sigset in self._signal_sets[signo]:
                self._signal_sets[signo].remove(sigset)

            # If there are no active watchers for a signal, revert it back to default behavior
            if not self._signal_sets[signo]:
                signal.signal(signo, self._default_signals[signo])
                del self._signal_sets[signo]

    def _shutdown_resources(self):
        log.debug('Kernel %r shutting down', self)
        if self._notify_sock:
            self._notify_sock.close()
            self._notify_sock = None
            self._wait_sock.close()
            self._wait_sock = None

        if self._signal_sets:
            signal.set_wakeup_fd(-1)
            self._signal_sets = None
            self._default_signals = None

        if self._iomanager:
            self._iomanager.close()
            self._iomanager = None

        if self._thread_pool:
            self._thread_pool.shutdown()
            self._thread_pool = None
        
        if self._process_pool:
            self._process_pool.shutdown()
            self._process_pool = None

    # Main Kernel Loop
    # ----------
    def run(self, coro=None, *, shutdown=False):
        '''
        Run the kernel until no more non-daemonic tasks remain.  If
        shutdown is True, the kernel cleans up after itself after all
        tasks complete.
        '''

        assert self._iomanager is not None, 'Kernel has been shut down'

        # Motto:  "What happens in the kernel stays in the kernel"

        # ---- Kernel State
        current = None                          # Currently running task
        iomanager = self._iomanager             # Event selector
        ready = self._ready                     # Ready queue
        tasks = self._tasks                     # Task table
        sleeping = self._sleeping               # Sleeping task queue
        wake_queue = self._wake_queue           # External wake queue

        # ---- Number of non-daemonic tasks running
        njobs = sum(not task.daemon for task in tasks.values())

        # ---- Bound methods
        iomanager_register = iomanager.register
        iomanager_unregister = iomanager.unregister
        iomanager_select = iomanager.select
        ready_popleft = ready.popleft
        ready_append = ready.append
        ready_appendleft = ready.appendleft
        time_monotonic = time.monotonic
        _wake = self._wake     

        # ---- In-kernel task used for processing signals and futures

        # Initialize the loopback socket and launch the kernel task if needed
        def _init_loopback_task():
            self._init_loopback()
            task = Task(_kernel_task(), taskid=0, daemon=True)
            _reschedule_task(task)
            self._kernel_task_id = task.id
            self._tasks[task.id] = task

        # Internal task that monitors the loopback socket--allowing the kernel to
        # awake for non-I/O events.  Also processes incoming signals.  This only
        # launches if needed to wait for external events (futures, signals, etc.)
        async def _kernel_task():
            wake_queue_popleft = wake_queue.popleft
            wait_sock = self._wait_sock

            while True:
                await _read_wait(wait_sock)
                data = wait_sock.recv(1000)

                # Process any waking tasks.  These are tasks that have been awakened
                # externally to the event loop (e.g., by separate threads, Futures, etc.)
                while wake_queue:
                    task, future = wake_queue_popleft()
                    # If the future associated with wakeup no longer matches
                    # the future stored on the task, wakeup is abandoned.
                    # It means that a timeout or cancellation event occurred
                    # in the time interval between the call to self._wake()
                    # and the subsequent processing of the waking task
                    if future and task.future is not future:
                        continue
                    task.future = None
                    task.state = 'READY'
                    task.cancel_func = None
                    ready_append(task)

                # Any non-null bytes received here are assumed to be received signals.
                # See if there are any pending signal sets and unblock if needed
                if not self._signal_sets:
                    continue

                sigs = (n for n in data if n in self._signal_sets)
                for signo in sigs:
                    for sigset in self._signal_sets[signo]:
                        sigset.pending.append(signo)
                        if sigset.waiting:
                            _reschedule_task(sigset.waiting, value=signo)
                            sigset.waiting = None

        # ---- Task Support Functions

        # Create a new task. Putting it on the ready queue
        def _new_task(coro, daemon=False):
            nonlocal njobs
            task = Task(coro, daemon)
            tasks[task.id] = task
            if not daemon:
                njobs += 1
            _reschedule_task(task)
            return task

        # Reschedule a task, putting it back on the ready queue so that it can run.
        # value and exc specify a value or exception to send into the underlying
        # coroutine when it is rescheduled.
        def _reschedule_task(task, value=None, exc=None):
            ready_append(task)
            task.next_value = value
            task.next_exc = exc
            task.state = 'READY'
            task.cancel_func = None

        # Cancel a task. This causes a CancelledError exception to raise in the
        # underlying coroutine.  The coroutine can elect to catch the exception
        # and continue to run to perform cleanup actions.  However, it would
        # normally terminate shortly afterwards.   This method is also used to
        # raise timeouts.
        def _cancel_task(task, exc=CancelledError, val=None):
            if task.terminated:
                return True

            if not task.cancel_func:
                # All tasks set a cancellation function when they
                # block.  If there is no cancellation function set. It
                # means that the task finished whatever it might have
                # been working on and it's sitting in the ready queue
                # ready to run.  This presents a rather tricky corner
                # case of cancellation. First, it means that the task
                # successfully completed whatever it was waiting to
                # do, but it has not yet communicated the result back.
                # This could be something critical like acquiring a
                # lock.  Because of that, can't just arbitrarily nuke
                # the task.  Instead, we have to let it be rescheduled
                # and properly process the result of the successfully
                # completed operation.  The return of False here means
                # that cancellation failed and that it should be
                # retried.  Public facing API calls that cancel tasks
                # need to check this return value and retry.
                return False

            # Detach the task from where it might be waiting at this moment
            task.cancel_func()

            # Reschedule it with a pending exception
            _reschedule_task(task, exc=exc(exc.__name__ if val is None else val))
            return True

        # Cleanup task.  This is called after the underlying coroutine has
        # terminated.  value and exc give the return value or exception of
        # the coroutine.  This wakes any tasks waiting to join.
        def _cleanup_task(task, value=None, exc=None):
            nonlocal njobs
            task.next_value = value
            task.next_exc = exc
            task.timeout = None

            if not task.daemon:
                njobs -= 1

            if task.joining:
                for wtask in task.joining:
                    _reschedule_task(wtask)
                task.joining = None
            task.terminated = True

            del tasks[task.id]

        # For "reasons" related to task scheduling, the task
        # of shutting down all remaining tasks is best managed
        # by a launching a task dedicated to carrying out the task (sic)
        async def _shutdown_tasks(tocancel):
            for task in tocancel:
                try:
                    await task.cancel()
                except Exception as e:
                    log.error('Exception %r ignored in curio shutdown' % e, exc_info=True)


        # Shut down the kernel. All remaining tasks are run through a cancellation
        # process so that they can cleanup properly.  After that, internal
        # resources are cleaned up.
        def _shutdown():
            nonlocal njobs
            tocancel = [task for task in tasks.values() if task.id != self._kernel_task_id]

            # Cancel all non-daemonic tasks first
            tocancel.sort(key=lambda task: task.daemon)

            # Cancel the kernel loopback task last
            if self._kernel_task_id is not None:
                tocancel.append(tasks[self._kernel_task_id])

            if tocancel:
                _new_task(_shutdown_tasks(tocancel))
                self.run()

            self._kernel_task_id = None

            # There had better not be any tasks left
            assert not tasks

            # Cleanup other resources
            self._shutdown_resources()

        # Set a timeout or sleep event on the current task
        def _set_timeout(clock, sleep_type='timeout'):
            item = (clock, current.id, sleep_type)
            heapq.heappush(sleeping, item)
            setattr(current, sleep_type, clock)

        # ---- Traps
        #
        # These implement the low-level functionality that is
        # triggered by coroutines.  They are never invoked directly
        # and there is no public API outside the kernel.  Instead,
        # coroutines use a statement such as
        #
        #   yield ('_trap_io', sock, EVENT_READ, 'READ_WAIT')
        #
        # to invoke a specific trap.

        # Wait for I/O
        def _trap_io(fileobj, event, state):
            iomanager_register(fileobj, event, current)
            current.state = state
            current.cancel_func = lambda task=current: iomanager_unregister(fileobj, event, task)

        # Wait on a Future
        def _trap_future_wait(future, event):
            if self._kernel_task_id is None:
                _init_loopback_task()

            current.state = 'FUTURE_WAIT'
            current.cancel_func = (lambda task=current:
                                   setattr(task, 'future', future.cancel() and None))
            current.future = future

            # Discussion: Each task records the future that it is
            # currently waiting on.  The completion callback below only
            # attempts to wake the task if its stored Future is exactly
            # the same one that was stored above.  Due to support for
            # cancellation and timeouts, it's possible that a task might
            # abandon its attempt to wait for a Future and go on to
            # perform other operations, including waiting for different
            # Future in the future (got it?).  However, a running thread
            # or process still might go on to eventually complete the
            # earlier work.  In that case, it will trigger the callback,
            # find that the task's current Future is now different, and
            # discard the result.

            future.add_done_callback(lambda fut, task=current: _wake(task, fut))

            # An optional threading.Event object can be passed and set to
            # start a worker thread.   This makes it possible to have a lock-free
            # Future implementation where worker threads only start after the
            # callback function has been set above.
            if event:
                event.set()

        # Add a new task to the kernel
        def _trap_spawn(coro, daemon):
            task = _new_task(coro, daemon)
            _copy_tasklocal(current, task)
            _reschedule_task(current, value=task)

        # Reschedule one or more tasks from a queue
        def _trap_reschedule_tasks(queue, n):
            for _ in range(n):
                _reschedule_task(queue.popleft())
            _reschedule_task(current)

        # Trap that returns a function for rescheduling tasks from synchronous code
        def _sync_trap_queue_reschedule_function(queue):
            def _reschedule(n):
                for _ in range(n):
                    _reschedule_task(queue.popleft())
            return _reschedule

        # Join with a task
        def _trap_join_task(task):
            if task.terminated:
                _reschedule_task(current)
            else:
                if task.joining is None:
                    task.joining = kqueue()
                _trap_wait_queue(task.joining, 'TASK_JOIN')

        # Enter or exit an 'async with curio.defer_cancellation' block:
        def _sync_trap_adjust_cancel_defer_depth(n):
            current.cancel_defer_depth += n
            if current.cancel_defer_depth == 0 and current.cancel_pending:
                current.cancel_pending = False
                if current.cancelled:
                    return
                raise CancelledError("CancelledError")

        # Cancel a task
        def _trap_cancel_task(task):
            if task == current:
                _reschedule_task(current, exc=CurioError("A task can't cancel itself"))
                return

            if task.cancelled:
                ready_appendleft(current)
            elif task.cancel_defer_depth > 0:
                task.cancel_pending = True
                ready_appendleft(current)
            elif _cancel_task(task, CancelledError):
                task.cancelled = True
                ready_appendleft(current)
            else:
                # Fail with a _CancelRetry exception to indicate that the cancel
                # request should be attempted again.  This happens in the case
                # that a cancellation request is issued against a task that
                # ready to run in the ready queue.
                _reschedule_task(current, exc=_CancelRetry())

        # Wait on a queue
        def _trap_wait_queue(queue, state):
            queue.append(current)
            current.state = state
            current.cancel_func = lambda current=current: queue.remove(current)

        # Sleep for a specified period. Returns value of monotonic clock.
        # absolute flag indicates whether or not an absolute or relative clock 
        # interval has been provided
        def _trap_sleep(clock, absolute):
            # We used to have a special case where sleep periods <= 0 would
            # simply reschedule the task to the end of the ready queue without
            # actually putting it on the sleep queue first. But this meant
            # that if a task looped while calling sleep(0), it would allow
            # other *ready* tasks to run, but block ever checking for I/O or
            # timeouts, so sleeping tasks would never wake up. That's not what
            # we want; sleep(0) should mean "please give other stuff a chance
            # to run". So now we always go through the whole sleep machinery.
            if not absolute:
                clock += time_monotonic()
            _set_timeout(clock, 'sleep')
            current.state = 'TIME_SLEEP'
            current.cancel_func = lambda task=current: setattr(task, 'sleep', None)

        # Watch signals
        def _sync_trap_sigwatch(sigset):
            # Initialize the signal handling part of the kernel if not done already
            # Note: This only works if running in the main thread
            if self._kernel_task_id is None:
                _init_loopback_task()

            if self._signal_sets is None:
                self._init_signals()

            self._signal_watch(sigset)

        # Unwatch signals
        def _sync_trap_sigunwatch(sigset):
            self._signal_unwatch(sigset)

        # Wait for a signal
        def _trap_sigwait(sigset):
            sigset.waiting = current
            current.state = 'SIGNAL_WAIT'
            current.cancel_func = lambda: setattr(sigset, 'waiting', None)

        # Set a timeout to be delivered to the calling task
        def _sync_trap_set_timeout(timeout):
            old_timeout = current.timeout
            if timeout:
                _set_timeout(timeout)
                if old_timeout and current.timeout > old_timeout:
                    current.timeout = old_timeout
            else:
                current.timeout = None

            return old_timeout

        # Clear a previously set timeout
        def _sync_trap_unset_timeout(previous):
            # Here's an evil corner case.  Suppose the previous timeout in effect
            # has already expired?  If so, then we need to arrange for a timeout
            # to be generated.  However, this has to happen on the *next* blocking
            # call, not on this trap.  That's because the "unset" timeout feature
            # is usually done in the finalization stage of the previous timeout
            # handling.  If we were to raise a TaskTimeout here, it would get mixed
            # up with the prior timeout handling and all manner of head-explosion
            # will occur.

            if previous and previous < time_monotonic():
                _set_timeout(previous)
            else:
                current.timeout = previous

        # Return the running kernel
        def _sync_trap_get_kernel():
            return self

        # Return the currently running task
        def _sync_trap_get_current():
            return current

        # Return the current value of the kernel clock
        def _sync_trap_clock():
            return time_monotonic()

        # Create the traps tables
        traps = [None] * len(Traps)
        for trap in Traps:
            traps[trap] = locals()[trap.name]

        sync_traps = [None] * len(SyncTraps)
        for trap in SyncTraps:
            sync_traps[trap] = locals()[trap.name]

        # If a coroutine was given, add it as the first task
        maintask = _new_task(coro) if coro else None

        # If there's no main-task and shutdown requested, perform the shutdown
        if maintask is None and shutdown:
            _shutdown()
            return

        # ------------------------------------------------------------
        # Main Kernel Loop
        # ------------------------------------------------------------
        while njobs > 0:
            # --------
            # Poll for I/O as long as there is nothing to run
            # --------
            while not ready:
                # Wait for an I/O event (or timeout)
                timeout = (sleeping[0][0] - time_monotonic()) if sleeping else None
                for task in iomanager_select(timeout):
                    task.state = 'READY'
                    task.cancel_func = None
                    ready_append(task)

                # Process sleeping tasks (if any)
                if sleeping:
                    current_time = time_monotonic()
                    cancel_retry = []
                    while sleeping and sleeping[0][0] <= current_time:
                        tm, taskid, sleep_type = heapq.heappop(sleeping)
                        # When a task wakes, verify that the timeout value matches that stored
                        # on the task. If it differs, it means that the task completed its
                        # operation, was cancelled, or is no longer concerned with this
                        # sleep operation.  In that case, we do nothing
                        if taskid in tasks:
                            task = tasks[taskid]
                            if sleep_type == 'sleep':
                                if tm == task.sleep:
                                    task.sleep = None
                                    _reschedule_task(task, value=current_time)
                            else:
                                if tm == task.timeout:
                                    if (_cancel_task(task, exc=TaskTimeout, val=current_time)):
                                        task.timeout = None
                                    else:
                                        # Note: There is a possibility that a task will be
                                        # marked for timeout-cancellation even though it is
                                        # sitting on the ready queue.  In this case, the
                                        # rescheduled task is given priority. However, the
                                        # cancellation timeout will be put back on the sleep
                                        # queue and reprocessed the next time around. 
                                        cancel_retry.append((tm, taskid, sleep_type))

                    # Put deferred cancellation requests back on sleep queue
                    for item in cancel_retry:
                        heapq.heappush(sleeping, item)

            # --------
            # Run ready tasks
            # --------
            while ready:
                current = ready_popleft()
                try:
                    current.state = 'RUNNING'
                    current.cycles += 1
                    with _enable_tasklocal_for(current):
                        if current.next_exc is None:
                            trap = current._send(current.next_value)
                            current.next_value = None
                        else:
                            trap = current._throw(current.next_exc)
                            current.next_exc = None

                        # If the trap is synchronous, then handle it
                        # immediately without rescheduling. Sync trap handlers
                        # have a different API than regular traps -- they just
                        # return or raise whatever the trap should return or
                        # raise.
                        while type(trap[0]) is SyncTraps:
                            try:
                                next_value = sync_traps[trap[0]](*trap[1:])
                            except Exception as next_exc:
                                trap = current._throw(next_exc)
                            else:
                                trap = current._send(next_value)

                except StopIteration as e:
                    _cleanup_task(current, value=e.value)

                except (CancelledError, TaskExit) as e:
                    current.exc_info = sys.exc_info()
                    current.state = 'CANCELLED'
                    _cleanup_task(current, exc=e)

                except Exception as e:
                    current.exc_info = sys.exc_info()
                    current.state = 'CRASHED'
                    exc = TaskError('Task Crashed')
                    exc.__cause__ = e
                    _cleanup_task(current, exc=exc)
                    if self._log_errors:
                        log.error('Curio: Task Crash: %s' % current, exc_info=True)

                    if self._crash_handler:
                        self._crash_handler(current)

                    if self._pdb:
                        import pdb as _pdb
                        _pdb.post_mortem(current.exc_info[2])

                except: # (SystemExit, KeyboardInterrupt):
                    _cleanup_task(current)
                    raise

                else:
                    # Execute the trap
                    assert type(trap[0]) is Traps
                    traps[trap[0]](*trap[1:])

        # If kernel shutdown has been requested, issue a cancellation request to all remaining tasks
        if shutdown:
            _shutdown()

        if maintask:
            if maintask.next_exc:
                raise maintask.next_exc
            else:
                return maintask.next_value
        else:
            return None

def run(coro, *, pdb=False, log_errors=True, with_monitor=False, selector=None, 
        crash_handler=None, **extra):
    '''
    Run the curio kernel with an initial task and execute until all
    tasks terminate.  Returns the task's final result (if any). This
    is a convenience function that should primarily be used for
    launching the top-level task of an curio-based application.  It
    creates an entirely new kernel, runs the given task to completion,
    and concludes by shutting down the kernel, releasing all resources used.

    Don't use this function if you're repeatedly launching a lot of
    new tasks to run in curio. Instead, create a Kernel instance and
    use its run() method instead.
    '''
    kernel = Kernel(selector=selector, with_monitor=with_monitor,
                    log_errors=log_errors, pdb=pdb, crash_handler=crash_handler, **extra)
    with kernel:
        result = kernel.run(coro)
    return result

__all__ = [ 'Kernel', 'run' ]

from .monitor import Monitor
