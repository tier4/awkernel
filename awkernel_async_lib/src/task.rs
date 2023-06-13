//! Task structure and functions.
//!
//! - `Task` represents a task. This is handled as `Arc<Task>`.
//!     - `Task::wake()` and `Task::wake_by_ref()` call `Task::scheduler::wake_task()` to wake the task up.
//!     - `Task::info`, which type is `TaskInfo`, contains information of the task.
//! - `TaskInfo` represents information of task.
//! - `Tasks` is a set of tasks.

#[cfg(not(feature = "no_preempt"))]
mod preempt;

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
    sync::atomic::{AtomicU32, Ordering},
    task::{Context, Poll},
};
use futures::{
    future::{BoxFuture, Fuse, FusedFuture},
    task::{waker_ref, ArcWake},
    Future, FutureExt,
};

#[cfg(not(feature = "no_preempt"))]
pub use preempt::{deallocate_thread_pool, get_num_preemption, preemption};

#[cfg(not(feature = "no_preempt"))]
use preempt::PtrWorkerThreadContext;

/// Return type of futures taken by `awkernel_async_lib::task::spawn`.
pub type TaskResult = Result<(), Cow<'static, str>>;

static TASKS: Mutex<Tasks> = Mutex::new(Tasks::new()); // Set of tasks.
static RUNNING: [AtomicU32; NUM_MAX_CPU] = array![_ => AtomicU32::new(0); NUM_MAX_CPU]; // IDs of running tasks.

/// Task has ID, future, information, and a reference to a scheduler.
pub struct Task {
    pub id: u32,
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
    last_executed_time: u64,

    #[cfg(not(feature = "no_preempt"))]
    thread: Option<PtrWorkerThreadContext>,
}

impl TaskInfo {
    #[cfg(not(feature = "no_preempt"))]
    pub(crate) fn take_preempt_context(&mut self) -> Option<PtrWorkerThreadContext> {
        self.thread.take()
    }

    #[cfg(not(feature = "no_preempt"))]
    pub(crate) fn set_preempt_context(&mut self, ctx: PtrWorkerThreadContext) {
        self.thread = Some(ctx)
    }

    pub fn get_state(&self) -> State {
        self.state
    }

    pub fn get_scheduler_type(&self) -> SchedulerType {
        self.scheduler_type
    }

    pub fn is_preempted(&self) -> bool {
        #[cfg(not(feature = "no_preempt"))]
        return self.thread.is_some();

        #[allow(unreachable_code)]
        false
    }

    pub fn update_last_executed(&mut self) {
        self.last_executed_time = awkernel_lib::delay::uptime();
    }

    pub fn get_last_executed(&self) -> u64 {
        self.last_executed_time
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
    candidate_id: u32, // Next candidate of task ID.
    id_to_task: BTreeMap<u32, Arc<Task>>,
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
    ) -> u32 {
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
                    last_executed_time: 0,

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

    fn wake(&self, id: u32) {
        if let Some(task) = self.id_to_task.get(&id) {
            task.clone().wake();
        }
    }

    fn remove(&mut self, id: u32) {
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
) -> u32 {
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
pub fn get_current_task(cpu_id: usize) -> Option<u32> {
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
        if let Some(next) = preempt::get_next_task() {
            return Some(next);
        }
    }

    scheduler::get_next_task()
}

pub fn run_main() {
    loop {
        if let Some(task) = get_next_task() {
            {
                let mut node = MCSNode::new();
                let mut info = task.info.lock(&mut node);

                info.update_last_executed();

                #[cfg(not(feature = "no_preempt"))]
                {
                    // If the next task is a preempted task, then the current task will yield to the thread holding the next task.
                    // After that, the current thread will be stored in the thread pool.

                    if let Some(ctx) = info.take_preempt_context() {
                        drop(info);

                        unsafe { preempt::yield_and_pool(ctx) };
                        continue;
                    }
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

                {
                    let cpu_id = awkernel_lib::cpu::cpu_id();
                    RUNNING[cpu_id].store(task.id, Ordering::Relaxed);
                }

                // Invoke a task.
                let result = {
                    catch_unwind(|| {
                        #[cfg(all(target_arch = "aarch64", not(feature = "std")))]
                        {
                            awkernel_lib::interrupt::enable();
                        }

                        #[allow(clippy::let_and_return)]
                        let result = guard.poll_unpin(&mut ctx);

                        #[cfg(all(target_arch = "aarch64", not(feature = "std")))]
                        {
                            awkernel_lib::interrupt::disable();
                        }

                        result
                    })
                };

                {
                    let cpu_id = awkernel_lib::cpu::cpu_id();
                    let running_id = RUNNING[cpu_id].swap(0, Ordering::Relaxed);
                    assert_eq!(running_id, task.id);
                }

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
pub unsafe fn run() {
    #[cfg(not(feature = "std"))]
    preempt::init();

    run_main();
}

/// Wake `task_id` up.
pub fn wake(task_id: u32) {
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

pub fn get_tasks_running() -> Vec<u32> {
    let mut tasks = Vec::new();
    let num_cpus = awkernel_lib::cpu::num_cpu();

    for (cpu_id, task) in RUNNING.iter().enumerate() {
        if cpu_id >= num_cpus {
            break;
        }

        tasks.push(task.load(Ordering::Relaxed));
    }

    tasks
}
