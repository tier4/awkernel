//! Task structure and functions.
//!
//! - `Task` represents a task. This is handled as `Arc<Task>`.
//!     - `Task::wake()` and `Task::wake_by_ref()` call `Task::scheduler::wake_task()` to wake the task up.
//!     - `Task::info`, which type is `TaskInfo`, contains information of the task.
//! - `TaskList` is a list of tasks.
//!     - This is used by schedulers. See `awkernel_async_lib::scheduler::round_robin`.
//!     - `TaskList::push()` takes `Arc<Task>` and pushes it to the tail.
//!     - `TaskList::pop()` returns `Arc<Task>` from the head.`
//! - `TaskInfo` represents information of task.
//!     - `TaskInfo::next` is used by `TaskList` to construct a linked list.
//! - `Tasks` is a set of tasks.

use crate::{
    delay::wait_microsec,
    scheduler::{self, get_scheduler, Scheduler, SchedulerType},
};
use alloc::{
    borrow::Cow,
    boxed::Box,
    collections::{btree_map, BTreeMap},
    sync::Arc,
};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::{
    any::Any,
    ptr::{read_volatile, write_volatile},
    task::{Context, Poll},
};
use futures::{
    future::{BoxFuture, Fuse, FusedFuture},
    task::{waker_ref, ArcWake},
    Future, FutureExt,
};

/// Return type of futures taken by `awkernel_async_lib::task::spawn`.
pub type TaskResult = Result<(), Cow<'static, str>>;

static TASKS: Mutex<Tasks> = Mutex::new(Tasks::new()); // Set of tasks.
static mut RUNNING: [Option<u64>; 512] = [None; 512]; // IDs of running tasks.

/// List of tasks.
pub(crate) struct TaskList {
    head: Option<Arc<Task>>,
    tail: Option<Arc<Task>>,
}

impl TaskList {
    pub(crate) fn new() -> Self {
        TaskList {
            head: None,
            tail: None,
        }
    }

    /// Push a task to the tail.
    pub(crate) fn push(&mut self, task: Arc<Task>) {
        if let Some(tail) = &self.tail {
            {
                let mut node = MCSNode::new();
                let mut info = tail.info.lock(&mut node);
                info.next = Some(task.clone());
            }

            self.tail = Some(task);
        } else {
            self.head = Some(task.clone());
            self.tail = Some(task);
        }
    }

    /// Pop a task from the head.
    pub(crate) fn pop(&mut self) -> Option<Arc<Task>> {
        if let Some(head) = self.head.take() {
            let next = {
                let mut node = MCSNode::new();
                let mut info = head.info.lock(&mut node);
                info.next.take()
            };

            if next.is_none() {
                self.tail = None;
            }
            self.head = next;

            Some(head)
        } else {
            None
        }
    }
}

/// Task has ID, future, information, and a reference to a scheduler.
pub(crate) struct Task {
    id: u64,
    future: Mutex<Fuse<BoxFuture<'static, TaskResult>>>,
    pub(crate) info: Mutex<TaskInfo>,
    scheduler: &'static dyn Scheduler,
}

unsafe impl Sync for Task {}
unsafe impl Send for Task {}

impl ArcWake for Task {
    fn wake_by_ref(arc_self: &Arc<Self>) {
        let cloned = arc_self.clone();
        cloned.wake();
    }

    fn wake(self: Arc<Self>) {
        self.scheduler.wake_task(self);
    }
}

/// Information of task.
#[derive(Clone)]
pub(crate) struct TaskInfo {
    pub(crate) state: State,
    pub(crate) _scheduler_type: SchedulerType,
    next: Option<Arc<Task>>,
}

/// State of task.
#[derive(Debug, Clone, Copy)]
pub(crate) enum State {
    Ready,
    Running,
    InQueue,
    Waiting,
    Terminated,
    Panicked,
}

/// Tasks.
#[derive(Default)]
struct Tasks {
    candidate_id: u64, // Next candidate of task ID.
    id_to_task: BTreeMap<u64, Arc<Task>>,
}

impl Tasks {
    const fn new() -> Self {
        Self {
            candidate_id: 0,
            id_to_task: BTreeMap::new(),
        }
    }

    fn spawn(
        &mut self,
        future: Fuse<BoxFuture<'static, TaskResult>>,
        scheduler: &'static dyn Scheduler,
        scheduler_type: SchedulerType,
    ) -> u64 {
        let mut id = self.candidate_id;
        loop {
            // Find an unused task ID.
            if let btree_map::Entry::Vacant(e) = self.id_to_task.entry(id) {
                let info = Mutex::new(TaskInfo {
                    _scheduler_type: scheduler_type,
                    state: State::Ready,
                    next: None,
                });

                let task = Task {
                    future: Mutex::new(future),
                    scheduler,
                    id,
                    info,
                };

                e.insert(Arc::new(task));
                self.candidate_id += 1;

                return id;
            } else {
                // The candidate task ID is already used.
                // Check next candidate.
                id += 1;
            }
        }
    }

    fn wake(&self, id: u64) {
        if let Some(task) = self.id_to_task.get(&id) {
            task.clone().wake();
        }
    }

    fn remove(&mut self, id: u64) {
        self.id_to_task.remove(&id);
    }
}

/// Spawn a detached task.
/// If you want to spawn tasks in non async functions,
/// use this function.
/// This function takes only futures that return `TaskResult`.
///
/// Use `awkernel_async_lib::spawn` in async functions instead of this.
/// `awkernel_async_lib::spawn` can take any future and joinable.
///
/// # Example
///
/// ```
/// use awkernel_async_lib::{scheduler::SchedulerType, task};
/// let task_id = task::spawn(async { Ok(()) }, SchedulerType::RoundRobin);
/// ```
pub fn spawn(
    future: impl Future<Output = TaskResult> + 'static + Send,
    sched_type: SchedulerType,
) -> u64 {
    let future = future.boxed();

    let scheduler = get_scheduler(sched_type);

    let mut node = MCSNode::new();
    let mut tasks = TASKS.lock(&mut node);
    let id = tasks.spawn(future.fuse(), scheduler, sched_type);
    tasks.wake(id);

    id
}

/// Get the task ID currently running.
///
/// # Example
///
/// ```
/// if let Some(task_id) = awkernel_async_lib::task::get_current_task(1) { }
/// ```
pub fn get_current_task(cpu_id: usize) -> Option<u64> {
    unsafe { read_volatile(&RUNNING[cpu_id]) }
}

/// Execute runnable tasks.
/// This function should be called worker threads.
/// So, do not call this function in application code.
pub fn run(cpu_id: usize) {
    loop {
        if let Some(task) = scheduler::get_next_task() {
            let w = waker_ref(&task);
            let mut ctx = Context::from_waker(&w);

            let mut node = MCSNode::new();
            let mut guard = task.future.lock(&mut node);

            unsafe { write_volatile(&mut RUNNING[cpu_id], Some(task.id)) };

            if guard.is_terminated() {
                continue;
            }

            // Use the primary memory allocator.
            #[cfg(not(feature = "std"))]
            unsafe {
                awkernel_lib::heap::TALLOC.use_primary()
            };

            // Invoke a task.
            let result = catch_unwind(|| guard.poll_unpin(&mut ctx));

            // If the primary memory allocator is available, it will be used.
            // If the primary memory allocator is exhausted, the backup allocator will be used.
            #[cfg(not(feature = "std"))]
            unsafe {
                awkernel_lib::heap::TALLOC.use_primary_then_backup()
            };

            match result {
                Ok(Poll::Pending) => {
                    // The task has not been terminated yet.
                    let mut node = MCSNode::new();
                    let mut info = task.info.lock(&mut node);
                    info.state = State::Waiting;
                }
                Ok(Poll::Ready(result)) => {
                    // The task has been terminated.

                    {
                        let mut node = MCSNode::new();
                        let mut info = task.info.lock(&mut node);
                        info.state = State::Terminated;
                    }

                    if let Err(msg) = result {
                        log::warn!("Task has been terminated but failed: {msg}");
                    }

                    let mut node = MCSNode::new();
                    let mut tasks = TASKS.lock(&mut node);
                    tasks.remove(task.id);
                }
                Err(err) => {
                    // Caught panic.

                    {
                        let mut node = MCSNode::new();
                        let mut info = task.info.lock(&mut node);
                        info.state = State::Panicked;
                    }

                    log::error!("Task has panicked!: {:?}", err);

                    let mut node = MCSNode::new();
                    let mut tasks = TASKS.lock(&mut node);
                    tasks.remove(task.id);
                }
            }
        } else {
            unsafe { write_volatile(&mut RUNNING[cpu_id], None) };

            #[cfg(target_os = "linux")]
            wait_microsec(10);

            #[cfg(not(target_os = "linux"))]
            wait_microsec(1);
        }
    }
}

#[cfg(feature = "std")]
fn catch_unwind<F, R>(f: F) -> Result<R, Box<(dyn Any + Send + 'static)>>
where
    F: FnOnce() -> R,
{
    use core::panic::AssertUnwindSafe;

    std::panic::catch_unwind(AssertUnwindSafe(f))
}

#[cfg(not(feature = "std"))]
fn catch_unwind<F, R>(f: F) -> Result<R, Box<(dyn Any + Send + 'static)>>
where
    F: FnOnce() -> R,
{
    use core::panic::AssertUnwindSafe;
    unwinding::panic::catch_unwind(AssertUnwindSafe(f))
}
