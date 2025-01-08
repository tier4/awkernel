//! Task structure and functions.
//!
//! - `Task` represents a task. This is handled as `Arc<Task>`.
//!     - `Task::wake()` and `Task::wake_by_ref()` call `Task::scheduler::wake_task()` to wake the task up.
//!     - `Task::info`, which type is `TaskInfo`, contains information of the task.
//! - `TaskInfo` represents information of task.
//! - `Tasks` is a set of tasks.

#[cfg(not(feature = "no_preempt"))]
mod preempt;

#[cfg(feature = "perf")]
use crate::cpu_counter;

use crate::scheduler::{self, get_scheduler, Scheduler, SchedulerType, IS_SEND_IPI};
use alloc::{
    borrow::Cow,
    collections::{btree_map, BTreeMap},
    sync::Arc,
};
use array_macro::array;
use awkernel_lib::{
    cpu::NUM_MAX_CPU,
    sync::mutex::{MCSNode, Mutex},
    unwind::catch_unwind,
};
use core::{
    sync::atomic::{AtomicBool, AtomicU32, AtomicU64, Ordering},
    task::{Context, Poll},
};
use futures::{
    future::{BoxFuture, Fuse, FusedFuture},
    task::{waker_ref, ArcWake},
    Future, FutureExt,
};

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

#[cfg(not(feature = "no_preempt"))]
pub use preempt::{preemption, thread::deallocate_thread_pool};

#[cfg(not(feature = "no_preempt"))]
use preempt::thread::PtrWorkerThreadContext;

/// Return type of futures taken by `awkernel_async_lib::task::spawn`.
pub type TaskResult = Result<(), Cow<'static, str>>;

static TASKS: Mutex<Tasks> = Mutex::new(Tasks::new()); // Set of tasks.
static RUNNING: [AtomicU32; NUM_MAX_CPU] = array![_ => AtomicU32::new(0); NUM_MAX_CPU]; // IDs of running tasks.
pub static NOT_IN_TRANSITION: [AtomicBool; NUM_MAX_CPU] =
    array![_ => AtomicBool::new(false); NUM_MAX_CPU]; // Whether or not RUNNING can be loaded.
static MAX_TASK_PRIORITY: u64 = (1 << 56) - 1; // Maximum task priority.

/// Task has ID, future, information, and a reference to a scheduler.
pub struct Task {
    pub id: u32,
    pub name: Cow<'static, str>,
    future: Mutex<Fuse<BoxFuture<'static, TaskResult>>>,
    pub info: Mutex<TaskInfo>,
    scheduler: &'static dyn Scheduler,
    pub priority: PriorityInfo,
}

impl Task {
    #[inline(always)]
    pub fn scheduler_name(&self) -> SchedulerType {
        self.scheduler.scheduler_name()
    }
}

unsafe impl Sync for Task {}
unsafe impl Send for Task {}

impl ArcWake for Task {
    fn wake_by_ref(arc_self: &Arc<Self>) {
        let cloned = arc_self.clone();
        cloned.wake();
    }

    fn wake(self: Arc<Self>) {
        let panicked;

        {
            use State::*;

            let mut node = MCSNode::new();
            let mut info = self.info.lock(&mut node);

            match info.state {
                Running | Runnable | Preempted => {
                    info.need_sched = true;
                    return;
                }
                Terminated | Panicked => {
                    return;
                }
                Ready | Waiting => {
                    info.state = Runnable;
                }
            }

            panicked = info.panicked;
        }

        if panicked {
            scheduler::panicked::SCHEDULER.wake_task(self);
        } else {
            self.scheduler.wake_task(self);
        }
    }
}

/// Information of task.
pub struct TaskInfo {
    pub(crate) state: State,
    pub(crate) scheduler_type: SchedulerType,
    pub(crate) num_preempt: u64,
    last_executed_time: u64,
    absolute_deadline: Option<u64>,
    need_sched: bool,
    need_preemption: bool,
    panicked: bool,

    #[cfg(not(feature = "no_preempt"))]
    thread: Option<PtrWorkerThreadContext>,
}

impl TaskInfo {
    #[cfg(not(feature = "no_preempt"))]
    #[inline(always)]
    pub(crate) fn take_preempt_context(&mut self) -> Option<PtrWorkerThreadContext> {
        self.thread.take()
    }

    #[cfg(not(feature = "no_preempt"))]
    #[inline(always)]
    pub(crate) fn set_preempt_context(&mut self, ctx: PtrWorkerThreadContext) {
        assert!(self.thread.is_none());
        self.thread = Some(ctx)
    }

    #[inline(always)]
    pub fn get_state(&self) -> State {
        self.state
    }

    #[inline(always)]
    pub fn get_scheduler_type(&self) -> SchedulerType {
        if self.panicked {
            SchedulerType::Panicked
        } else {
            self.scheduler_type
        }
    }

    #[inline(always)]
    pub fn update_last_executed(&mut self) {
        self.last_executed_time = awkernel_lib::delay::uptime();
    }

    #[inline(always)]
    pub fn get_last_executed(&self) -> u64 {
        self.last_executed_time
    }

    #[inline(always)]
    pub fn update_absolute_deadline(&mut self, deadline: u64) {
        self.absolute_deadline = Some(deadline);
    }

    #[inline(always)]
    pub fn get_absolute_deadline(&self) -> Option<u64> {
        self.absolute_deadline
    }

    #[inline(always)]
    pub fn get_num_preemption(&self) -> u64 {
        self.num_preempt
    }

    #[inline(always)]
    pub fn panicked(&self) -> bool {
        self.panicked
    }
}

/// State of task.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum State {
    Ready,
    Running,
    Runnable,
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
                    absolute_deadline: None,
                    need_sched: false,
                    need_preemption: false,
                    panicked: false,

                    #[cfg(not(feature = "no_preempt"))]
                    thread: None,
                });

                // Set the task priority.
                // If the scheduler implements dynamic priority scheduling, the task priority will be updated later.
                let task_priority = match scheduler_type {
                    SchedulerType::PrioritizedFIFO(priority)
                    | SchedulerType::PriorityBasedRR(priority) => priority as u64,
                    _ => MAX_TASK_PRIORITY,
                };

                let task = Task {
                    name,
                    future: Mutex::new(future),
                    scheduler,
                    id,
                    info,
                    priority: PriorityInfo::new(scheduler.priority(), task_priority),
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

    #[inline(always)]
    fn wake(&self, id: u32) {
        if let Some(task) = self.id_to_task.get(&id) {
            task.clone().wake();
        }
    }

    #[inline(always)]
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
/// let task_id = task::spawn("example task".into(), async { Ok(()) }, SchedulerType::FIFO);
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
    let task = tasks.id_to_task.get(&id).cloned();
    drop(tasks);

    if let Some(task) = task {
        task.wake();
    }

    id
}

/// Get the task ID currently running.
///
/// # Example
///
/// ```
/// if let Some(task_id) = awkernel_async_lib::task::get_current_task(1) { }
/// ```
#[inline(always)]
pub fn get_current_task(cpu_id: usize) -> Option<u32> {
    let id = RUNNING[cpu_id].load(Ordering::Relaxed);
    if id == 0 {
        None
    } else {
        Some(id)
    }
}

#[inline(always)]
fn get_next_task() -> Option<Arc<Task>> {
    #[cfg(not(feature = "no_preempt"))]
    {
        if let Some(next) = preempt::get_next_task() {
            return Some(next);
        }
    }

    scheduler::get_next_task()
}

#[cfg(feature = "perf")]
pub mod perf {
    use crate::task::get_current_task;
    use awkernel_lib::cpu::NUM_MAX_CPU;
    use core::ptr::{addr_of, read_volatile, write_volatile};
    use core::sync::atomic::{AtomicUsize, Ordering};

    pub const MAX_MEASURE_SIZE: usize = 1024 * 8;

    static mut TASK_EXEC_TIMES_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut TASK_EXEC_TIMES_PER_TASK: [u64; MAX_MEASURE_SIZE] = [0; MAX_MEASURE_SIZE];
    static mut TASK_EXEC_TIMES_PER_CPU: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];

    static mut KERNEL_TIMES_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut KERNEL_TIMES_SUM: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];

    static mut IDLE_TIMES_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut IDLE_TIMES_SUM: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];

    static mut YIELD_CONTEXT_SAVE_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut YIELD_CONTEXT_SAVE_OVERHEADS: [u64; MAX_MEASURE_SIZE] = [0; MAX_MEASURE_SIZE];
    static mut YIELD_CONTEXT_SAVE_OVERHEADS_PER_CPU: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static YIELD_CSO_COUNT: AtomicUsize = AtomicUsize::new(0);
    static mut YIELD_CONTEXT_RESTORE_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut YIELD_CONTEXT_RESTORE_OVERHEADS: [u64; MAX_MEASURE_SIZE] = [0; MAX_MEASURE_SIZE];
    static mut YIELD_CONTEXT_RESTORE_OVERHEADS_PER_CPU: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static YIELD_CRO_COUNT: AtomicUsize = AtomicUsize::new(0);

    static mut PREEMPT_CONTEXT_SAVE_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut PREEMPT_CONTEXT_SAVE_OVERHEADS: [u64; MAX_MEASURE_SIZE] = [0; MAX_MEASURE_SIZE];
    static mut PREEMPT_CONTEXT_SAVE_OVERHEADS_PER_CPU: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static PREEMPT_CSO_COUNT: AtomicUsize = AtomicUsize::new(0);
    static mut PREEMPT_CONTEXT_RESTORE_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut PREEMPT_CONTEXT_RESTORE_OVERHEADS: [u64; MAX_MEASURE_SIZE] = [0; MAX_MEASURE_SIZE];
    static mut PREEMPT_CONTEXT_RESTORE_OVERHEADS_PER_CPU: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static PREEMPT_CRO_COUNT: AtomicUsize = AtomicUsize::new(0);

    pub enum ContextSwitchType {
        Yield,
        Preempt,
    }

    pub fn add_task_start(cpu_id: usize, time: u64) {
        unsafe { write_volatile(&mut TASK_EXEC_TIMES_STARTS[cpu_id], time) };
    }

    pub fn add_task_end(cpu_id: usize, time: u64) {
        let task_id = get_current_task(cpu_id).unwrap_or(0);
        if task_id == 0 {
            log::warn!("CPUID#{:?} is not running any task", cpu_id);
            return;
        }
        let task_index = (task_id as usize) & (MAX_MEASURE_SIZE - 1);
        let start = unsafe { read_volatile(&TASK_EXEC_TIMES_STARTS[cpu_id]) };

        if start != 0 && time > start {
            let current_exec_time = time - start;
            unsafe {
                let sum_cpu_time = read_volatile(&TASK_EXEC_TIMES_PER_CPU[cpu_id]);
                write_volatile(
                    &mut TASK_EXEC_TIMES_PER_CPU[cpu_id],
                    current_exec_time + sum_cpu_time,
                );
                let sum_task_exec_time = read_volatile(&TASK_EXEC_TIMES_PER_TASK[task_index]);
                write_volatile(
                    &mut TASK_EXEC_TIMES_PER_TASK[task_index],
                    current_exec_time + sum_task_exec_time,
                );
                write_volatile(&mut TASK_EXEC_TIMES_STARTS[cpu_id], 0);
            }
        }
    }

    pub fn reset_task_exec_time(task_id: u32) {
        let task_index = (task_id as usize) & (MAX_MEASURE_SIZE - 1);
        unsafe { write_volatile(&mut TASK_EXEC_TIMES_PER_TASK[task_index], 0) };
    }

    pub fn get_task_exec_time(task_id: u32) -> u64 {
        let task_index = (task_id as usize) & (MAX_MEASURE_SIZE - 1);
        unsafe { read_volatile(&TASK_EXEC_TIMES_PER_TASK[task_index]) }
    }

    pub fn get_cpu_time(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&TASK_EXEC_TIMES_PER_CPU[cpu_id]) }
    }

    pub fn add_kernel_time_start(cpu_id: usize, time: u64) {
        unsafe { write_volatile(&mut KERNEL_TIMES_STARTS[cpu_id], time) };
    }

    pub fn add_kernel_time_end(cpu_id: usize, time: u64) {
        let start = unsafe { read_volatile(&KERNEL_TIMES_STARTS[cpu_id]) };

        if start != 0 && time > start {
            let current_exec_time = time - start;
            unsafe {
                let sum_idle_time = read_volatile(&KERNEL_TIMES_SUM[cpu_id]);
                write_volatile(
                    &mut KERNEL_TIMES_SUM[cpu_id],
                    current_exec_time + sum_idle_time,
                );
                write_volatile(&mut KERNEL_TIMES_STARTS[cpu_id], 0)
            };
        }
    }

    pub fn get_kernel_time(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&KERNEL_TIMES_SUM[cpu_id]) }
    }

    pub fn add_idle_time_start(cpu_id: usize, time: u64) {
        unsafe { write_volatile(&mut IDLE_TIMES_STARTS[cpu_id], time) };
    }

    pub fn add_idle_time_end(cpu_id: usize, time: u64) {
        let start = unsafe { read_volatile(&IDLE_TIMES_STARTS[cpu_id]) };

        if start != 0 && time > start {
            let current_exec_time = time - start;
            unsafe {
                let sum_idle_time = read_volatile(&IDLE_TIMES_SUM[cpu_id]);
                write_volatile(
                    &mut IDLE_TIMES_SUM[cpu_id],
                    current_exec_time + sum_idle_time,
                );
                write_volatile(&mut IDLE_TIMES_STARTS[cpu_id], 0)
            };
        }
    }

    pub fn get_idle_time(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&IDLE_TIMES_SUM[cpu_id]) }
    }

    pub fn add_context_save_start(context_type: ContextSwitchType, cpu_id: usize, time: u64) {
        unsafe {
            match context_type {
                ContextSwitchType::Yield => {
                    write_volatile(&mut YIELD_CONTEXT_SAVE_STARTS[cpu_id], time)
                }
                ContextSwitchType::Preempt => {
                    write_volatile(&mut PREEMPT_CONTEXT_SAVE_STARTS[cpu_id], time)
                }
            }
        };
    }

    pub fn add_context_save_end(context_type: ContextSwitchType, cpu_id: usize, time: u64) {
        let start = unsafe {
            match context_type {
                ContextSwitchType::Yield => read_volatile(&YIELD_CONTEXT_SAVE_STARTS[cpu_id]),
                ContextSwitchType::Preempt => read_volatile(&PREEMPT_CONTEXT_SAVE_STARTS[cpu_id]),
            }
        };

        if start != 0 && time > start {
            let context_save_overhead = time - start;

            let index = match context_type {
                ContextSwitchType::Yield => YIELD_CSO_COUNT.fetch_add(1, Ordering::Relaxed),
                ContextSwitchType::Preempt => PREEMPT_CSO_COUNT.fetch_add(1, Ordering::Relaxed),
            };

            unsafe {
                match context_type {
                    ContextSwitchType::Yield => {
                        write_volatile(
                            &mut YIELD_CONTEXT_SAVE_OVERHEADS[index & (MAX_MEASURE_SIZE - 1)],
                            context_save_overhead,
                        );
                        let sum_context_save_overhead =
                            read_volatile(&YIELD_CONTEXT_SAVE_OVERHEADS_PER_CPU[cpu_id]);
                        write_volatile(
                            &mut YIELD_CONTEXT_SAVE_OVERHEADS_PER_CPU[cpu_id],
                            context_save_overhead + sum_context_save_overhead,
                        );
                        write_volatile(&mut YIELD_CONTEXT_SAVE_STARTS[cpu_id], 0);
                    }
                    ContextSwitchType::Preempt => {
                        write_volatile(
                            &mut PREEMPT_CONTEXT_SAVE_OVERHEADS[index & (MAX_MEASURE_SIZE - 1)],
                            context_save_overhead,
                        );
                        let sum_context_save_overhead =
                            read_volatile(&PREEMPT_CONTEXT_SAVE_OVERHEADS_PER_CPU[cpu_id]);
                        write_volatile(
                            &mut PREEMPT_CONTEXT_SAVE_OVERHEADS_PER_CPU[cpu_id],
                            context_save_overhead + sum_context_save_overhead,
                        );
                        write_volatile(&mut PREEMPT_CONTEXT_SAVE_STARTS[cpu_id], 0);
                    }
                }
            };
        }
    }

    pub fn add_context_restore_start(context_type: ContextSwitchType, cpu_id: usize, time: u64) {
        unsafe {
            match context_type {
                ContextSwitchType::Yield => {
                    write_volatile(&mut YIELD_CONTEXT_RESTORE_STARTS[cpu_id], time)
                }
                ContextSwitchType::Preempt => {
                    write_volatile(&mut PREEMPT_CONTEXT_RESTORE_STARTS[cpu_id], time)
                }
            }
        }
    }

    pub fn add_context_restore_end(context_type: ContextSwitchType, cpu_id: usize, time: u64) {
        let start = unsafe {
            match context_type {
                ContextSwitchType::Yield => read_volatile(&YIELD_CONTEXT_RESTORE_STARTS[cpu_id]),
                ContextSwitchType::Preempt => {
                    read_volatile(&PREEMPT_CONTEXT_RESTORE_STARTS[cpu_id])
                }
            }
        };

        if start != 0 && time > start {
            let context_restore_overhead = time - start;

            let index = match context_type {
                ContextSwitchType::Yield => YIELD_CRO_COUNT.fetch_add(1, Ordering::Relaxed),
                ContextSwitchType::Preempt => PREEMPT_CRO_COUNT.fetch_add(1, Ordering::Relaxed),
            };

            unsafe {
                match context_type {
                    ContextSwitchType::Yield => {
                        write_volatile(
                            &mut YIELD_CONTEXT_RESTORE_OVERHEADS[index & (MAX_MEASURE_SIZE - 1)],
                            context_restore_overhead,
                        );
                        let sum_context_restore_overhead =
                            read_volatile(&YIELD_CONTEXT_RESTORE_OVERHEADS_PER_CPU[cpu_id]);
                        write_volatile(
                            &mut YIELD_CONTEXT_RESTORE_OVERHEADS_PER_CPU[cpu_id],
                            context_restore_overhead + sum_context_restore_overhead,
                        );
                        write_volatile(&mut YIELD_CONTEXT_RESTORE_STARTS[cpu_id], 0);
                    }
                    ContextSwitchType::Preempt => {
                        write_volatile(
                            &mut PREEMPT_CONTEXT_RESTORE_OVERHEADS[index & (MAX_MEASURE_SIZE - 1)],
                            context_restore_overhead,
                        );
                        let sum_context_restore_overhead =
                            read_volatile(&PREEMPT_CONTEXT_RESTORE_OVERHEADS_PER_CPU[cpu_id]);
                        write_volatile(
                            &mut PREEMPT_CONTEXT_RESTORE_OVERHEADS_PER_CPU[cpu_id],
                            context_restore_overhead + sum_context_restore_overhead,
                        );
                        write_volatile(&mut PREEMPT_CONTEXT_RESTORE_STARTS[cpu_id], 0);
                    }
                }
            };
        }
    }

    pub fn get_overheads(context_type: ContextSwitchType, cpu_id: usize) -> (u64, u64) {
        unsafe {
            match context_type {
                ContextSwitchType::Yield => {
                    let save = read_volatile(&YIELD_CONTEXT_SAVE_OVERHEADS_PER_CPU[cpu_id]);
                    let restore = read_volatile(&YIELD_CONTEXT_RESTORE_OVERHEADS_PER_CPU[cpu_id]);
                    (save, restore)
                }
                ContextSwitchType::Preempt => {
                    let save = read_volatile(&PREEMPT_CONTEXT_SAVE_OVERHEADS_PER_CPU[cpu_id]);
                    let restore = read_volatile(&PREEMPT_CONTEXT_RESTORE_OVERHEADS_PER_CPU[cpu_id]);
                    (save, restore)
                }
            }
        }
    }

    fn calc_overheads(overheads: &[u64; MAX_MEASURE_SIZE]) -> (f64, f64) {
        let mut total = 0;
        let mut count = 0;
        let mut worst = 0;

        #[allow(clippy::needless_range_loop)]
        for i in 0..MAX_MEASURE_SIZE {
            let overhead = unsafe { read_volatile(&overheads[i]) };
            if overhead > 0 {
                total += overhead;
                count += 1;
                if overhead > worst {
                    worst = overhead;
                }
            }
        }

        if count > 0 {
            (total as f64 / count as f64, worst as f64)
        } else {
            (0.0, 0.0)
        }
    }

    pub fn calc_context_switch_overhead(context_type: ContextSwitchType) -> (f64, f64, f64, f64) {
        let (avg_save, worst_save, avg_restore, worst_restore) = match context_type {
            ContextSwitchType::Yield => {
                let (avg_save, worst_save) =
                    calc_overheads(unsafe { &*addr_of!(YIELD_CONTEXT_SAVE_OVERHEADS) });
                let (avg_restore, worst_restore) =
                    calc_overheads(unsafe { &*addr_of!(YIELD_CONTEXT_RESTORE_OVERHEADS) });
                (avg_save, worst_save, avg_restore, worst_restore)
            }
            ContextSwitchType::Preempt => {
                let (avg_save, worst_save) =
                    calc_overheads(unsafe { &*addr_of!(PREEMPT_CONTEXT_SAVE_OVERHEADS) });
                let (avg_restore, worst_restore) =
                    calc_overheads(unsafe { &*addr_of!(PREEMPT_CONTEXT_RESTORE_OVERHEADS) });
                (avg_save, worst_save, avg_restore, worst_restore)
            }
        };

        (avg_save, worst_save, avg_restore, worst_restore)
    }
}

pub fn run_main() {
    loop {
        #[cfg(feature = "perf")]
        perf::add_kernel_time_start(awkernel_lib::cpu::cpu_id(), cpu_counter());

        if let Some(task) = get_next_task() {
            NOT_IN_TRANSITION[awkernel_lib::cpu::cpu_id()].store(false, Ordering::Relaxed);
            #[cfg(not(feature = "no_preempt"))]
            {
                // If the next task is a preempted task, then the current task will yield to the thread holding the next task.
                // After that, the current thread will be stored in the thread pool.
                let mut node = MCSNode::new();
                let mut info = task.info.lock(&mut node);

                if let Some(ctx) = info.take_preempt_context() {
                    info.update_last_executed();
                    drop(info);

                    #[cfg(feature = "perf")]
                    {
                        perf::add_kernel_time_end(awkernel_lib::cpu::cpu_id(), cpu_counter());
                        perf::add_context_save_start(
                            perf::ContextSwitchType::Yield,
                            awkernel_lib::cpu::cpu_id(),
                            cpu_counter(),
                        );
                    }

                    unsafe { preempt::yield_and_pool(ctx) };

                    #[cfg(feature = "perf")]
                    {
                        perf::add_context_restore_end(
                            perf::ContextSwitchType::Yield,
                            awkernel_lib::cpu::cpu_id(),
                            cpu_counter(),
                        );
                        perf::add_kernel_time_start(awkernel_lib::cpu::cpu_id(), cpu_counter());
                    }

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
                }

                let cpu_id = awkernel_lib::cpu::cpu_id();

                // Use the primary memory allocator.
                #[cfg(not(feature = "std"))]
                unsafe {
                    awkernel_lib::heap::TALLOC.use_primary_cpu_id(cpu_id)
                };

                RUNNING[cpu_id].store(task.id, Ordering::Relaxed);
                NOT_IN_TRANSITION[cpu_id].store(true, Ordering::Relaxed);

                // Invoke a task.
                catch_unwind(|| {
                    #[cfg(all(
                        any(target_arch = "aarch64", target_arch = "x86_64"),
                        not(feature = "std")
                    ))]
                    {
                        awkernel_lib::interrupt::enable();
                    }

                    #[cfg(feature = "perf")]
                    {
                        perf::add_kernel_time_end(awkernel_lib::cpu::cpu_id(), cpu_counter());
                        perf::add_task_start(cpu_id, cpu_counter());
                    }

                    #[allow(clippy::let_and_return)]
                    let result = guard.poll_unpin(&mut ctx);

                    #[cfg(feature = "perf")]
                    {
                        perf::add_task_end(awkernel_lib::cpu::cpu_id(), cpu_counter());
                        perf::add_kernel_time_start(awkernel_lib::cpu::cpu_id(), cpu_counter());
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

            let cpu_id = awkernel_lib::cpu::cpu_id();

            // If the primary memory allocator is available, it will be used.
            // If the primary memory allocator is exhausted, the backup allocator will be used.
            #[cfg(not(feature = "std"))]
            unsafe {
                awkernel_lib::heap::TALLOC.use_primary_then_backup_cpu_id(cpu_id)
            };

            let running_id = RUNNING[cpu_id].swap(0, Ordering::Relaxed);
            assert_eq!(running_id, task.id);

            let mut node = MCSNode::new();
            let mut info = task.info.lock(&mut node);

            match result {
                Ok(Poll::Pending) => {
                    // The task has not been terminated yet.
                    info.state = State::Waiting;

                    if info.need_sched {
                        info.need_sched = false;
                        drop(info);
                        task.clone().wake();
                    }

                    #[cfg(feature = "perf")]
                    perf::add_kernel_time_end(awkernel_lib::cpu::cpu_id(), cpu_counter());
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

                    #[cfg(feature = "perf")]
                    perf::reset_task_exec_time(task.id);

                    tasks.remove(task.id);

                    #[cfg(feature = "perf")]
                    perf::add_kernel_time_end(awkernel_lib::cpu::cpu_id(), cpu_counter());
                }
                Err(_) => {
                    // Caught panic.
                    info.state = State::Panicked;
                    drop(info);

                    let mut node = MCSNode::new();
                    let mut tasks = TASKS.lock(&mut node);

                    #[cfg(feature = "perf")]
                    perf::reset_task_exec_time(task.id);
                    tasks.remove(task.id);

                    #[cfg(feature = "perf")]
                    perf::add_kernel_time_end(awkernel_lib::cpu::cpu_id(), cpu_counter());
                }
            }
        } else {
            NOT_IN_TRANSITION[awkernel_lib::cpu::cpu_id()].store(true, Ordering::Relaxed);
            #[cfg(feature = "perf")]
            perf::add_idle_time_start(awkernel_lib::cpu::cpu_id(), cpu_counter());

            #[cfg(feature = "std")]
            awkernel_lib::delay::wait_microsec(50);

            #[cfg(not(feature = "std"))]
            {
                if awkernel_lib::timer::is_timer_enabled() {
                    let _int_guard = awkernel_lib::interrupt::InterruptGuard::new();
                    awkernel_lib::interrupt::enable();
                    awkernel_lib::timer::reset();
                    awkernel_lib::delay::wait_interrupt();
                    awkernel_lib::timer::disable();
                } else {
                    awkernel_lib::delay::wait_microsec(10);
                }
            }

            #[cfg(feature = "perf")]
            perf::add_idle_time_end(awkernel_lib::cpu::cpu_id(), cpu_counter());
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
#[inline(always)]
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

#[inline(always)]
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

#[inline(always)]
pub fn get_last_executed_by_task_id(task_id: u32) -> Option<u64> {
    let mut node = MCSNode::new();
    let tasks = TASKS.lock(&mut node);

    tasks.id_to_task.get(&task_id).map(|task| {
        let mut node = MCSNode::new();
        let info = task.info.lock(&mut node);
        info.get_last_executed()
    })
}

#[inline(always)]
pub fn get_scheduler_type_by_task_id(task_id: u32) -> Option<SchedulerType> {
    let mut node = MCSNode::new();
    let tasks = TASKS.lock(&mut node);

    tasks.id_to_task.get(&task_id).map(|task| {
        let mut node = MCSNode::new();
        let info = task.info.lock(&mut node);
        info.get_scheduler_type()
    })
}

#[inline(always)]
pub fn get_absolute_deadline_by_task_id(task_id: u32) -> Option<u64> {
    let mut node = MCSNode::new();
    let tasks = TASKS.lock(&mut node);

    tasks.id_to_task.get(&task_id).and_then(|task| {
        let mut node = MCSNode::new();
        let info = task.info.lock(&mut node);
        info.get_absolute_deadline()
    })
}

#[inline(always)]
pub fn set_need_preemption(task_id: u32) {
    let mut node = MCSNode::new();
    let tasks = TASKS.lock(&mut node);

    if let Some(task) = tasks.id_to_task.get(&task_id) {
        let mut node = MCSNode::new();
        let mut info = task.info.lock(&mut node);
        info.need_preemption = true;
    }
}

pub fn panicking() {
    let Some(task_id) = get_current_task(awkernel_lib::cpu::cpu_id()) else {
        return;
    };

    {
        let mut node = MCSNode::new();
        let tasks = TASKS.lock(&mut node);

        if let Some(task) = tasks.id_to_task.get(&task_id) {
            let mut node = MCSNode::new();
            let mut info = task.info.lock(&mut node);
            info.scheduler_type = SchedulerType::Panicked;
            info.panicked = true;
        } else {
            #[allow(clippy::needless_return)]
            return;
        }
    }

    #[cfg(not(feature = "no_preempt"))]
    unsafe {
        preempt::preemption();
    }
}

pub struct PriorityInfo {
    pub priority: AtomicU64,
}

impl PriorityInfo {
    fn new(scheduler_priority: u8, task_priority: u64) -> Self {
        PriorityInfo {
            priority: AtomicU64::new(Self::combine_priority(scheduler_priority, task_priority)),
        }
    }

    pub fn update_priority_info(&self, scheduler_priority: u8, task_priority: u64) {
        self.priority.store(
            Self::combine_priority(scheduler_priority, task_priority),
            Ordering::Relaxed,
        );
    }

    fn combine_priority(scheduler_priority: u8, task_priority: u64) -> u64 {
        assert!(task_priority < (1 << 56), "Task priority exceeds 56 bits");
        ((scheduler_priority as u64) << 56) | (task_priority & ((1 << 56) - 1))
    }
}

impl Clone for PriorityInfo {
    fn clone(&self) -> Self {
        let value = self.priority.load(Ordering::Relaxed);
        PriorityInfo {
            priority: AtomicU64::new(value),
        }
    }
}

impl PartialEq for PriorityInfo {
    fn eq(&self, other: &Self) -> bool {
        self.priority.load(Ordering::Relaxed) == other.priority.load(Ordering::Relaxed)
    }
}

impl Eq for PriorityInfo {}

impl PartialOrd for PriorityInfo {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PriorityInfo {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.priority
            .load(Ordering::Relaxed)
            .cmp(&other.priority.load(Ordering::Relaxed))
    }
}

pub fn get_lowest_priority_task_info() -> Option<(u32, usize, PriorityInfo)> {
    let non_primary_cpus = awkernel_lib::cpu::num_cpu().saturating_sub(1);
    let mut lowest_task: Option<(u32, usize, PriorityInfo)> = None; // (task_id, cpu_id, priority_info)

    loop {
        // Wait until all task statuses are ready to load.
        loop {
            let true_count = NOT_IN_TRANSITION
                .iter()
                .filter(|flag| flag.load(Ordering::Relaxed))
                .count();

            if true_count >= non_primary_cpus {
                break;
            }
        }

        let running_tasks: Vec<RunningTask> = get_tasks_running()
            .into_iter()
            .filter(|task| task.task_id != 0)
            .collect();

        if running_tasks.len() != non_primary_cpus {
            return None;
        }

        let priority_infos: Vec<(u32, usize, PriorityInfo)> = {
            let mut node = MCSNode::new();
            let tasks = TASKS.lock(&mut node);
            running_tasks
                .into_iter()
                .filter_map(|task| {
                    tasks
                        .id_to_task
                        .get(&task.task_id)
                        .map(|task_data| (task.task_id, task.cpu_id, task_data.priority.clone()))
                })
                .collect()
        };

        for (task_id, cpu_id, priority_info) in priority_infos {
            if lowest_task
                .as_ref()
                .is_none_or(|(_, _, lowest_priority_info)| priority_info > *lowest_priority_info)
            {
                lowest_task = Some((task_id, cpu_id, priority_info));
            }
        }

        // Check to confirm that the information has not changed while getting priority_info.
        if let Some((task_id, cpu_id, _)) = lowest_task {
            if !IS_SEND_IPI.load(Ordering::Relaxed)
                && NOT_IN_TRANSITION[cpu_id].load(Ordering::Relaxed)
                && RUNNING[cpu_id].load(Ordering::Relaxed) == task_id
            {
                break;
            }
        } else {
            lowest_task = None;
        }
    }

    lowest_task
}
