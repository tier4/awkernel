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
    delay::uptime,
    sync::mutex::{MCSNode, Mutex},
    unwind::catch_unwind,
    POLL_TIMESTAMPS,
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
pub use preempt::{preemption, thread::deallocate_thread_pool};

#[cfg(not(feature = "no_preempt"))]
use preempt::thread::PtrWorkerThreadContext;

/// Return type of futures taken by `awkernel_async_lib::task::spawn`.
pub type TaskResult = Result<(), Cow<'static, str>>;

static TASKS: Mutex<Tasks> = Mutex::new(Tasks::new()); // Set of tasks.
static RUNNING: [AtomicU32; NUM_MAX_CPU] = array![_ => AtomicU32::new(0); NUM_MAX_CPU]; // IDs of running tasks.

/// Task has ID, future, information, and a reference to a scheduler.
pub struct Task {
    pub id: u32,
    pub name: Cow<'static, str>,
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
        {
            use State::*;

            let mut node = MCSNode::new();
            let mut info = self.info.lock(&mut node);
            if matches!(info.state, Running | ReadyToRun | Preempted) {
                info.need_sched = true;
                return;
            } else if matches!(info.state, Terminated | Panicked) {
                return;
            }
        }

        self.scheduler.wake_task(self);
    }
}

/// Information of task.
pub struct TaskInfo {
    pub(crate) state: State,
    pub(crate) scheduler_type: SchedulerType,
    pub(crate) num_preempt: u64,
    last_executed_time: u64,
    pub(crate) in_queue: bool,
    need_sched: bool,
    poll_save_time: u64,
    poll_restore_time: u64,

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
        assert!(self.thread.is_none());
        self.thread = Some(ctx)
    }

    pub fn get_state(&self) -> State {
        self.state
    }

    pub fn get_scheduler_type(&self) -> SchedulerType {
        self.scheduler_type
    }

    pub fn update_last_executed(&mut self) {
        self.last_executed_time = awkernel_lib::delay::uptime();
    }

    pub fn get_last_executed(&self) -> u64 {
        self.last_executed_time
    }

    pub fn get_num_preemption(&self) -> u64 {
        self.num_preempt
    }

    pub fn in_queue(&self) -> bool {
        self.in_queue
    }
}

/// State of task.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum State {
    Ready,
    ReadyToRun,
    Running,
    Waiting,
    Preempted,
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
        name: Cow<'static, str>,
        future: Fuse<BoxFuture<'static, TaskResult>>,
        scheduler: &'static dyn Scheduler,
        scheduler_type: SchedulerType,
    ) -> u32 {
        let mut id = self.candidate_id;
        loop {
            if id == 0 {
                id += 1;
            }

            // Find an unused task ID.
            if let btree_map::Entry::Vacant(e) = self.id_to_task.entry(id) {
                let info = Mutex::new(TaskInfo {
                    scheduler_type,
                    state: State::Ready,
                    num_preempt: 0,
                    last_executed_time: 0,
                    in_queue: false,
                    need_sched: false,
                    poll_save_time: 0,
                    poll_restore_time: 0,

                    #[cfg(not(feature = "no_preempt"))]
                    thread: None,
                });

                let task = Task {
                    name,
                    future: Mutex::new(future),
                    scheduler,
                    id,
                    info,
                };

                e.insert(Arc::new(task));
                self.candidate_id = id;

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
/// let task_id = task::spawn(async { Ok(()) }, SchedulerType::FIFO);
/// ```
pub fn spawn(
    name: Cow<'static, str>,
    future: impl Future<Output = TaskResult> + 'static + Send,
    sched_type: SchedulerType,
) -> u32 {
    let future = future.boxed();

    let scheduler = get_scheduler(sched_type);

    let mut node = MCSNode::new();
    let mut tasks = TASKS.lock(&mut node);
    let id = tasks.spawn(name, future.fuse(), scheduler, sched_type);
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

fn measure_uptime_overhead(duration: usize) -> f64 {
    // Calculating overhead for one uptime() call
    let mut sum_uptime_time = 0.0;
    for _ in 0..duration {
        let start = uptime();
        uptime();
        let end = uptime();
        sum_uptime_time += (end - start) as f64 / 3.0;
    }
    sum_uptime_time / duration as f64
}

fn update_times(task: &Task, switch_time: &mut Vec<u64>, restore_start: u64, save_end: u64) {
    let mut local_node = MCSNode::new();
    let mut my_global = POLL_TIMESTAMPS[awkernel_lib::cpu::cpu_id()].lock(&mut local_node);

    let mut task_node = MCSNode::new();
    let mut info = task.info.lock(&mut task_node);

    if my_global.0 != 0 {
        info.poll_save_time = save_end - my_global.0;
        my_global.0 = 0;
    }
    if my_global.1 != 0 {
        info.poll_restore_time = my_global.1 - restore_start;
        my_global.1 = 0;
    }

    if info.poll_save_time != 0 && info.poll_restore_time != 0 {
        switch_time.push(info.poll_save_time + info.poll_restore_time);
        info.poll_save_time = 0;
        info.poll_restore_time = 0;
    }
}

pub fn run_main() {
    const DURATION: usize = 100000;
    let mut exe_time: Vec<u64> = Vec::new();
    let mut switch_time: Vec<u64> = Vec::new();
    let mut dur_start = 0;
    let uptime_overhead = measure_uptime_overhead(DURATION);

    loop {
        if let Some(task) = get_next_task() {
            #[cfg(not(feature = "no_preempt"))]
            {
                // If the next task is a preempted task, then the current task will yield to the thread holding the next task.
                // After that, the current thread will be stored in the thread pool.
                let mut node = MCSNode::new();
                let mut info = task.info.lock(&mut node);

                if let Some(ctx) = info.take_preempt_context() {
                    info.update_last_executed();
                    info.state = State::Running;
                    drop(info);

                    unsafe { preempt::yield_and_pool(ctx) };
                    continue;
                }
            }

            let w = waker_ref(&task);
            let mut ctx = Context::from_waker(&w);

            let result = {
                let mut node = MCSNode::new();
                let Some(mut guard) = task.future.try_lock(&mut node) else {
                    // This task is running on another CPU,
                    // and re-schedule the task to avoid starvation just in case.
                    task.wake();
                    continue;
                };

                // Can remove this?
                if guard.is_terminated() {
                    continue;
                }

                {
                    let mut node = MCSNode::new();
                    let mut info = task.info.lock(&mut node);

                    if matches!(info.state, State::Terminated | State::Panicked) {
                        continue;
                    }

                    info.update_last_executed();
                    info.state = State::Running;
                    info.need_sched = false;
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
                catch_unwind(|| {
                    #[cfg(all(
                        any(target_arch = "aarch64", target_arch = "x86_64"),
                        not(feature = "std")
                    ))]
                    {
                        awkernel_lib::interrupt::enable();
                    }

                    // Start task execution
                    let exe_start = uptime();
                    // duration start time is the first time of task execution
                    if exe_time.is_empty() {
                        dur_start = exe_start;
                    }

                    // Start poll() restore
                    let restore_start = uptime();

                    #[allow(clippy::let_and_return)]
                    let result = guard.poll_unpin(&mut ctx);

                    // End poll() save
                    let save_end = uptime();
                    // Update switch time
                    update_times(&task, &mut switch_time, restore_start, save_end);

                    // End task execution and end duration time if DURATION is reached
                    let exe_end = uptime();
                    exe_time.push(exe_end - exe_start);

                    if exe_time.len() % DURATION == 0 {
                        let cpu_id = awkernel_lib::cpu::cpu_id();
                        // Calculate CPU utilization during the DURATION time
                        let total_time = (exe_end - dur_start) as f64;
                        let total_overhead = (uptime_overhead * 2.0
                            + (restore_start - exe_start) as f64
                            + (exe_end - save_end) as f64)
                            * DURATION as f64;
                        log::info!(
                            "CPU#{:?} utilization = {:.3} [%]",
                            cpu_id,
                            exe_time.iter().sum::<u64>() as f64 / (total_time - total_overhead)
                                * 100.0,
                        );
                        exe_time.clear();

                        // Calculate average switch time during the DURATION time
                        log::info!(
                            "CPU#{:?} switch time = ave: {:.3} [us]",
                            cpu_id,
                            switch_time.iter().sum::<u64>() as f64 / switch_time.len() as f64,
                        );
                    }

                    #[cfg(all(
                        any(target_arch = "aarch64", target_arch = "x86_64"),
                        not(feature = "std")
                    ))]
                    {
                        awkernel_lib::interrupt::disable();
                    }

                    result
                })
            };

            // If the primary memory allocator is available, it will be used.
            // If the primary memory allocator is exhausted, the backup allocator will be used.
            #[cfg(not(feature = "std"))]
            unsafe {
                awkernel_lib::heap::TALLOC.use_primary_then_backup()
            };

            let cpu_id = awkernel_lib::cpu::cpu_id();
            let running_id = RUNNING[cpu_id].swap(0, Ordering::Relaxed);
            assert_eq!(running_id, task.id);

            let mut node = MCSNode::new();
            let mut info = task.info.lock(&mut node);

            match result {
                Ok(Poll::Pending) => {
                    info.state = State::Waiting;

                    if info.need_sched {
                        info.need_sched = false;
                        drop(info);
                        task.clone().wake();
                    }
                }
                Ok(Poll::Ready(result)) => {
                    // The task has been terminated.

                    info.state = State::Terminated;
                    drop(info);

                    if let Err(msg) = result {
                        log::warn!("Task has been terminated but failed: {msg}");
                    }

                    let mut node = MCSNode::new();
                    let mut tasks = TASKS.lock(&mut node);
                    tasks.remove(task.id);
                }
                Err(err) => {
                    // Caught panic.
                    info.state = State::Panicked;
                    drop(info);

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

#[derive(Debug)]
pub struct RunningTask {
    pub cpu_id: usize,
    pub task_id: u32,
}

pub fn get_tasks_running() -> Vec<RunningTask> {
    let mut tasks = Vec::new();
    let num_cpus = awkernel_lib::cpu::num_cpu();

    for (cpu_id, task) in RUNNING.iter().enumerate() {
        if cpu_id >= num_cpus {
            break;
        }

        let task_id = task.load(Ordering::Relaxed);
        tasks.push(RunningTask { cpu_id, task_id });
    }

    tasks
}

pub fn get_num_preemption() -> usize {
    #[cfg(not(feature = "no_preempt"))]
    {
        preempt::get_num_preemption()
    }

    #[cfg(feature = "no_preempt")]
    {
        0
    }
}
