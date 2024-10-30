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
    cpu_counter,
    scheduler::{self, get_scheduler, Scheduler, SchedulerType},
};
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
    sync::atomic::{AtomicU32, AtomicUsize, Ordering},
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
static CPUID_TO_RAWCPUID: [AtomicUsize; NUM_MAX_CPU] =
    array![_ => AtomicUsize::new(0); NUM_MAX_CPU]; // CPU ID to RAW CPU ID

/// Task has ID, future, information, and a reference to a scheduler.
pub struct Task {
    pub id: u32,
    pub name: Cow<'static, str>,
    future: Mutex<Fuse<BoxFuture<'static, TaskResult>>>,
    pub info: Mutex<TaskInfo>,
    scheduler: &'static dyn Scheduler,
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
                    need_sched: false,
                    need_preemption: false,
                    panicked: false,

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

pub mod perf {
    use crate::task::get_current_task;
    use awkernel_lib::cpu::NUM_MAX_CPU;
    use core::ptr::{addr_of, read_volatile, write_volatile};
    use core::sync::atomic::{AtomicUsize, Ordering};

    pub const MAX_MEASURE_SIZE: usize = 1024 * 8;

    static mut TASKS_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut TASKS_EXEC_TIMES: [u64; MAX_MEASURE_SIZE] = [0; MAX_MEASURE_SIZE];

    static mut YIELD_CONTEXT_SAVE_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut YIELD_CONTEXT_SAVE_OVERHEADS: [u64; MAX_MEASURE_SIZE] = [0; MAX_MEASURE_SIZE];
    static YIELD_CSO_COUNT: AtomicUsize = AtomicUsize::new(0);
    static mut YIELD_CONTEXT_RESTORE_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut YIELD_CONTEXT_RESTORE_OVERHEADS: [u64; MAX_MEASURE_SIZE] = [0; MAX_MEASURE_SIZE];
    static YIELD_CRO_COUNT: AtomicUsize = AtomicUsize::new(0);

    static mut PREEMPT_CONTEXT_SAVE_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut PREEMPT_CONTEXT_SAVE_OVERHEADS: [u64; MAX_MEASURE_SIZE] = [0; MAX_MEASURE_SIZE];
    static PREEMPT_CSO_COUNT: AtomicUsize = AtomicUsize::new(0);
    static mut PREEMPT_CONTEXT_RESTORE_STARTS: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut PREEMPT_CONTEXT_RESTORE_OVERHEADS: [u64; MAX_MEASURE_SIZE] = [0; MAX_MEASURE_SIZE];
    static PREEMPT_CRO_COUNT: AtomicUsize = AtomicUsize::new(0);

    pub enum ContextSwitchType {
        Yield,
        Preempt,
    }

    pub fn add_task_start(cpu_id: usize, time: u64) {
        unsafe { write_volatile(&mut TASKS_STARTS[cpu_id], time) };
    }

    pub fn add_task_end(cpu_id: usize, time: u64) {
        let task_id = get_current_task(cpu_id).unwrap_or(0);
        if task_id == 0 {
            log::warn!("CPUID#{:?} is not running any task", cpu_id);
            return;
        }
        let task_index = (task_id as usize) & (MAX_MEASURE_SIZE - 1);
        let start = unsafe { read_volatile(&TASKS_STARTS[cpu_id]) };

        if start != 0 && time > start {
            let current_exec_time = time - start;
            unsafe {
                let sum_exec_time = read_volatile(&TASKS_EXEC_TIMES[task_index]);
                write_volatile(
                    &mut TASKS_EXEC_TIMES[task_index],
                    current_exec_time + sum_exec_time,
                );
                write_volatile(&mut TASKS_STARTS[cpu_id], 0);
            }
        }
    }

    pub fn reset_task_exec(task_id: u32) {
        let task_index = (task_id as usize) & (MAX_MEASURE_SIZE - 1);
        unsafe { write_volatile(&mut TASKS_EXEC_TIMES[task_index], 0) };
    }

    pub fn get_task_exec(task_id: u32) -> u64 {
        let task_index = (task_id as usize) & (MAX_MEASURE_SIZE - 1);
        unsafe { read_volatile(&TASKS_EXEC_TIMES[task_index]) }
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
                        write_volatile(&mut YIELD_CONTEXT_SAVE_STARTS[cpu_id], 0);
                    }
                    ContextSwitchType::Preempt => {
                        write_volatile(
                            &mut PREEMPT_CONTEXT_SAVE_OVERHEADS[index & (MAX_MEASURE_SIZE - 1)],
                            context_save_overhead,
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
                        write_volatile(&mut YIELD_CONTEXT_RESTORE_STARTS[cpu_id], 0);
                    }
                    ContextSwitchType::Preempt => {
                        write_volatile(
                            &mut PREEMPT_CONTEXT_RESTORE_OVERHEADS[index & (MAX_MEASURE_SIZE - 1)],
                            context_restore_overhead,
                        );
                        write_volatile(&mut PREEMPT_CONTEXT_RESTORE_STARTS[cpu_id], 0);
                    }
                }
            };
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
    CPUID_TO_RAWCPUID[awkernel_lib::cpu::cpu_id()]
        .store(awkernel_lib::cpu::raw_cpu_id(), Ordering::Relaxed);

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
                }

                // Use the primary memory allocator.
                #[cfg(not(feature = "std"))]
                unsafe {
                    awkernel_lib::heap::TALLOC.use_primary()
                };

                let cpu_id = awkernel_lib::cpu::cpu_id();
                RUNNING[cpu_id].store(task.id, Ordering::Relaxed);

                // Invoke a task.
                catch_unwind(|| {
                    #[cfg(all(
                        any(target_arch = "aarch64", target_arch = "x86_64"),
                        not(feature = "std")
                    ))]
                    {
                        awkernel_lib::interrupt::enable();
                    }

                    perf::add_task_start(cpu_id, cpu_counter());

                    #[allow(clippy::let_and_return)]
                    let result = guard.poll_unpin(&mut ctx);

                    perf::add_task_end(awkernel_lib::cpu::cpu_id(), cpu_counter());

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
                    // The task has not been terminated yet.
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
                    perf::reset_task_exec(task.id);
                    tasks.remove(task.id);
                }
                Err(_) => {
                    // Caught panic.
                    info.state = State::Panicked;
                    drop(info);

                    let mut node = MCSNode::new();
                    let mut tasks = TASKS.lock(&mut node);
                    perf::reset_task_exec(task.id);
                    tasks.remove(task.id);
                }
            }
        } else {
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
pub fn get_raw_cpu_id(cpu_id: usize) -> usize {
    CPUID_TO_RAWCPUID[cpu_id].load(Ordering::Relaxed)
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
