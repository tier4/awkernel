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
    collections::{btree_map, BTreeMap},
    sync::Arc,
    vec::Vec,
};
use array_macro::array;
use awkernel_lib::{
    cpu::NUM_MAX_CPU,
    sync::mutex::{MCSNode, Mutex},
    unwind::catch_unwind,
};
use core::{
    sync::atomic::{AtomicU64, Ordering},
    task::{Context, Poll},
};
use futures::{
    future::{BoxFuture, Fuse, FusedFuture},
    task::{waker_ref, ArcWake},
    Future, FutureExt,
};

#[cfg(not(feature = "no_preempt"))]
pub use preempt::deallocate_thread_pool;

#[cfg(not(feature = "no_preempt"))]
use crate::preempt::{self, current_context, PtrWorkerThreadContext};

#[cfg(not(feature = "no_preempt"))]
use alloc::collections::LinkedList;

#[cfg(not(feature = "no_preempt"))]
use awkernel_lib::interrupt::{self, InterruptGuard};

/// Return type of futures taken by `awkernel_async_lib::task::spawn`.
pub type TaskResult = Result<(), Cow<'static, str>>;

static TASKS: Mutex<Tasks> = Mutex::new(Tasks::new()); // Set of tasks.
static RUNNING: [AtomicU64; NUM_MAX_CPU] = array![_ => AtomicU64::new(0); NUM_MAX_CPU]; // IDs of running tasks.

#[cfg(not(feature = "no_preempt"))]
static NEXT_TASK: Mutex<BTreeMap<usize, LinkedList<Arc<Task>>>> = Mutex::new(BTreeMap::new());

/// List of tasks.
pub(crate) struct TaskList {
    head: Option<Arc<Task>>,
    tail: Option<Arc<Task>>,
}

impl TaskList {
    pub(crate) const fn new() -> Self {
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
pub struct Task {
    pub id: u64,
    future: Mutex<Fuse<BoxFuture<'static, TaskResult>>>,
    pub info: Mutex<TaskInfo>,
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
pub struct TaskInfo {
    pub(crate) state: State,
    pub(crate) scheduler_type: SchedulerType,
    next: Option<Arc<Task>>,

    #[cfg(not(feature = "no_preempt"))]
    thread: Option<PtrWorkerThreadContext>,
}

impl TaskInfo {
    #[cfg(not(feature = "no_preempt"))]
    fn preempt_context(&mut self) -> Option<PtrWorkerThreadContext> {
        self.thread.take()
    }

    pub fn get_state(&self) -> State {
        self.state
    }

    pub fn get_scheduler_type(&self) -> SchedulerType {
        self.scheduler_type
    }
}

/// State of task.
#[derive(Debug, Clone, Copy)]
pub enum State {
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
            candidate_id: 1,
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
            if self.candidate_id == 0 {
                self.candidate_id += 1;
            }

            // Find an unused task ID.
            if let btree_map::Entry::Vacant(e) = self.id_to_task.entry(id) {
                let info = Mutex::new(TaskInfo {
                    scheduler_type,
                    state: State::Ready,
                    next: None,

                    #[cfg(not(feature = "no_preempt"))]
                    thread: None,
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
    let id = RUNNING[cpu_id].load(Ordering::Relaxed);
    if id == 0 {
        None
    } else {
        Some(id)
    }
}

fn get_next_task() -> Option<Arc<Task>> {
    #[cfg(not(feature = "no_preempt"))]
    {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        let mut node = MCSNode::new();
        let mut next_task = NEXT_TASK.lock(&mut node);
        if let Some(tasks) = next_task.get_mut(&cpu_id) {
            if let Some(task) = tasks.pop_front() {
                return Some(task);
            }
        }
    }

    scheduler::get_next_task()
}

pub fn run_main() {
    loop {
        if let Some(task) = get_next_task() {
            #[cfg(not(feature = "no_preempt"))]
            {
                // If the next task is a preempted task, then the current task will yield to the thread holding the next task.
                // After that, the current thread will be stored in the thread pool.

                let mut node = MCSNode::new();
                let mut info = task.info.lock(&mut node);

                if let Some(ctx) = info.preempt_context() {
                    drop(info);

                    unsafe { preempt::yield_and_pool(ctx) };
                    continue;
                }
            }

            let w = waker_ref(&task);
            let mut ctx = Context::from_waker(&w);

            let result = {
                let mut node = MCSNode::new();
                let mut guard = task.future.lock(&mut node);

                if guard.is_terminated() {
                    continue;
                }

                // Use the primary memory allocator.
                #[cfg(not(feature = "std"))]
                unsafe {
                    awkernel_lib::heap::TALLOC.use_primary()
                };

                let cpu_id = awkernel_lib::cpu::cpu_id();

                RUNNING[cpu_id].store(task.id, Ordering::Relaxed);

                // Invoke a task.
                let result = {
                    catch_unwind(|| {
                        #[cfg(all(target_arch = "aarch64", not(feature = "std")))]
                        awkernel_lib::interrupt::enable();

                        let result = guard.poll_unpin(&mut ctx);

                        #[cfg(all(target_arch = "aarch64", not(feature = "std")))]
                        awkernel_lib::interrupt::disable();
                        result
                    })
                };

                RUNNING[cpu_id].store(0, Ordering::Relaxed);

                result
            };

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
            #[cfg(feature = "std")]
            wait_microsec(10);

            #[cfg(not(feature = "std"))]
            wait_microsec(1);
        }
    }
}

/// Execute runnable tasks.
///
/// # Safety
///
/// This function must be called from worker threads.
/// So, do not call this function in application code.
pub unsafe fn run(_cpu_id: usize) {
    #[cfg(not(feature = "std"))]
    preempt::init(_cpu_id);

    run_main();
}

#[cfg(not(feature = "no_preempt"))]
pub unsafe fn preemption() {
    let _int_guard = InterruptGuard::new();

    #[cfg(not(feature = "std"))]
    let _heap_guard = {
        let heap_guard = awkernel_lib::heap::TALLOC.save();
        awkernel_lib::heap::TALLOC.use_primary();
        heap_guard
    };

    if let Err(e) = catch_unwind(|| do_preemption()) {
        #[cfg(not(feature = "std"))]
        awkernel_lib::heap::TALLOC.use_primary_then_backup();

        log::error!("caught panic!: {e:?}");
    }
}

#[cfg(not(feature = "no_preempt"))]
unsafe fn do_preemption() {
    let cpu_id = awkernel_lib::cpu::cpu_id();
    let current_thread = current_context();

    // If there is a running task on this CPU core, preemption is performed.
    // Otherwise, this function just returns.
    let task_id = RUNNING[cpu_id].load(Ordering::Relaxed);
    if task_id == 0 {
        return;
    }

    // If there is a task to be invoked next, execute the task.
    if let Some(next) = scheduler::get_next_task() {
        let current_task = {
            let mut node = MCSNode::new();
            let tasks = TASKS.lock(&mut node);

            // Make the current running task preempted.
            {
                let current_task = tasks.id_to_task.get(&task_id).unwrap();
                let mut node = MCSNode::new();
                let mut task_info = current_task.info.lock(&mut node);

                task_info.thread = Some(current_thread);

                current_task.clone()
            }
        };

        if let Some(next_thread) = {
            let mut node = MCSNode::new();
            let mut task_info = next.info.lock(&mut node);
            task_info.preempt_context()
        } {
            // If the next task is a preempted task, yield to it.
            preempt::yield_preempted_and_wake_task(next_thread, current_task);
        } else {
            // Otherwise, get a thread from the thread pool or create a new thread.

            let next_thread = if let Some(t) = preempt::get_pooled_thread() {
                // If there is a thread in the thread pool, use it,
                t
            } else if let Ok(t) = preempt::new_thread(thread_entry, 0) {
                // or create a new thread.
                t
            } else {
                next.wake();
                return;
            };

            {
                let mut node = MCSNode::new();
                let mut next_task = NEXT_TASK.lock(&mut node);

                // Insert the next task to the queue.
                match next_task.entry(cpu_id) {
                    btree_map::Entry::Occupied(mut entry) => {
                        entry.get_mut().push_back(next);
                    }
                    btree_map::Entry::Vacant(entry) => {
                        let mut queue = LinkedList::new();
                        queue.push_back(next);
                        entry.insert(queue);
                    }
                }
            }

            preempt::yield_preempted_and_wake_task(next_thread, current_task);
        }
    }
}

#[cfg(not(feature = "no_preempt"))]
#[no_mangle]
extern "C" fn thread_entry(_arg: usize) -> ! {
    // Use only the primary heap memory region.
    #[cfg(not(feature = "std"))]
    unsafe {
        awkernel_lib::heap::TALLOC.use_primary()
    };

    // Disable interrupt.
    interrupt::disable();

    // Re-schedule the preempted task.
    preempt::re_schedule();

    // Run the main function.
    run_main();

    awkernel_lib::delay::wait_forever();
}

/// Wake `task_id` up.
pub fn wake(task_id: u64) {
    let mut node = MCSNode::new();
    let gurad = TASKS.lock(&mut node);
    gurad.wake(task_id);
}

pub fn get_tasks() -> Vec<Arc<Task>> {
    let mut result = Vec::new();

    let mut node = MCSNode::new();
    let tasks = TASKS.lock(&mut node);

    for (_, task) in tasks.id_to_task.iter() {
        result.push(task.clone());
    }

    result
}
