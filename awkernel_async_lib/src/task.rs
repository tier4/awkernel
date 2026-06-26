//! Task structure and functions.
//!
//! - `Task` represents a task. This is handled as `Arc<Task>`.
//!     - `Task::wake()` and `Task::wake_by_ref()` call `Task::scheduler::wake_task()` to wake the task up.
//!     - `Task::info`, which type is `TaskInfo`, contains information of the task.
//! - `TaskInfo` represents information of task.
//! - `Tasks` is a set of tasks.

#[cfg(not(feature = "no_preempt"))]
mod preempt;

use crate::scheduler::{self, get_scheduler, pop_preemption_pending, Scheduler, SchedulerType};
use alloc::{
    borrow::Cow,
    collections::{btree_map, BTreeMap},
    sync::Arc,
};
use array_macro::array;
use awkernel_lib::{
    cpu::{num_cpu, NUM_MAX_CPU},
    priority_queue::HIGHEST_PRIORITY,
    sync::mutex::{MCSNode, Mutex},
    unwind::catch_unwind,
};
#[cfg(target_pointer_width = "64")]
use core::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, Ordering};

#[cfg(target_pointer_width = "32")]
use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};

use core::task::{Context, Poll};
use futures::{
    future::{BoxFuture, Fuse, FusedFuture},
    task::{waker_ref, ArcWake},
    Future, FutureExt,
};

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

#[cfg(not(feature = "no_preempt"))]
pub use preempt::{preemption, thread::deallocate_thread_pool, voluntary_preemption};

#[cfg(not(feature = "no_preempt"))]
use preempt::thread::PtrWorkerThreadContext;

/// Return type of futures taken by `awkernel_async_lib::task::spawn`.
pub type TaskResult = Result<(), Cow<'static, str>>;

static TASKS: Mutex<Tasks> = Mutex::new(Tasks::new()); // Set of tasks.
static RUNNING: [AtomicU32; NUM_MAX_CPU] = array![_ => AtomicU32::new(0); NUM_MAX_CPU]; // IDs of running tasks.
pub(crate) static MAX_TASK_PRIORITY: u64 = (1 << 56) - 1; // Maximum task priority.
#[cfg(target_pointer_width = "64")]
pub(crate) static NUM_TASK_IN_QUEUE: AtomicU32 = AtomicU32::new(0); // Number of tasks in the queue.

pub(crate) static NUM_PARTITIONED_TASKS_IN_QUEUE: [AtomicU32; NUM_MAX_CPU] =
    array![_ => AtomicU32::new(0); NUM_MAX_CPU];

#[cfg(target_pointer_width = "32")]
pub(crate) static NUM_TASK_IN_QUEUE: AtomicU32 = AtomicU32::new(0); // Number of tasks in the queue.

static PREEMPTION_REQUEST: [AtomicBool; NUM_MAX_CPU] =
    array![_ => AtomicBool::new(false); NUM_MAX_CPU];

/// Task has ID, future, information, and a reference to a scheduler.
pub struct Task {
    pub id: u32,
    pub name: Cow<'static, str>,
    future: Mutex<Fuse<BoxFuture<'static, TaskResult>>>,
    pub info: Mutex<TaskInfo>,
    scheduler: &'static dyn Scheduler,
    pub priority: PriorityInfo,
    pub partitioned_core: Option<u16>, // The core to which the task is statically assigned in partitioned scheduling. None if not assigned.
}

impl Task {
    #[inline(always)]
    pub fn scheduler_name(&self) -> SchedulerType {
        self.scheduler.scheduler_name()
    }
}

impl PartialEq for Task {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Task {}

impl PartialOrd for Task {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Task {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        // Higher (larger) priority is greater.
        match self.priority.cmp(&other.priority) {
            core::cmp::Ordering::Equal => self.id.cmp(&other.id),
            ord => ord,
        }
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
                Initialized | Waiting => {
                    info.state = Runnable;
                }
            }

            panicked = info.panicked;
        }

        // Panicked tasks go to the global panicked scheduler, so always use the global counter.
        // Non-panicked partitioned tasks: counter is managed inside partitioned_edf::wake_task.
        // Non-panicked non-partitioned tasks: increment the global counter here.
        if panicked || self.partitioned_core.is_none() {
            NUM_TASK_IN_QUEUE.fetch_add(1, Ordering::Release);
        }

        if panicked {
            scheduler::panicked::SCHEDULER.wake_task(self);
        } else {
            self.scheduler.wake_task(self);
        }

        // Notify the primary CPU to wake up workers.
        awkernel_lib::cpu::wake_cpu(0);
    }
}

/// Information of task.
pub struct TaskInfo {
    pub(crate) state: State,
    pub(crate) scheduler_type: SchedulerType,
    pub(crate) num_preempt: u64,
    last_executed_time: awkernel_lib::time::Time,
    absolute_deadline: Option<u64>,
    need_sched: bool,
    pub(crate) need_preemption: bool,
    panicked: bool,
    pub(crate) dag_info: Option<DagInfo>,

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
        self.last_executed_time = awkernel_lib::time::Time::now();
    }

    #[inline(always)]
    pub fn get_last_executed(&self) -> awkernel_lib::time::Time {
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

    #[inline(always)]
    pub fn get_dag_info(&self) -> Option<DagInfo> {
        self.dag_info.clone()
    }
}

/// State of task.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum State {
    Initialized,
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

#[derive(Clone)]
pub struct DagInfo {
    pub dag_id: u32,
    pub node_id: u32,
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
        mut scheduler_type: SchedulerType,
        dag_info: Option<DagInfo>,
    ) -> u32 {
        let mut id = self.candidate_id;
        loop {
            if id == 0 {
                id += 1;
            }

            // Find an unused task ID.
            if let btree_map::Entry::Vacant(e) = self.id_to_task.entry(id) {
                // Validate and normalise the partitioned core before creating TaskInfo so that
                // info.scheduler_type and task.partitioned_core stay in sync.
                let partitioned_core = if let SchedulerType::PartitionedEDF(deadline, core) =
                    scheduler_type
                {
                    if core == 0 || core >= num_cpu() as u16 {
                        log::warn!(
                            "Partitioned core should be between 1 and {}. Falling back to core 1. Given core: {}",
                            num_cpu() - 1,
                            core
                        );
                        scheduler_type = SchedulerType::PartitionedEDF(deadline, 1);
                        Some(1u16)
                    } else {
                        Some(core)
                    }
                } else {
                    None
                };

                let info = Mutex::new(TaskInfo {
                    scheduler_type,
                    state: State::Initialized,
                    num_preempt: 0,
                    last_executed_time: awkernel_lib::time::Time::now(),
                    absolute_deadline: None,
                    need_sched: false,
                    need_preemption: false,
                    panicked: false,
                    dag_info,

                    #[cfg(not(feature = "no_preempt"))]
                    thread: None,
                });

                // Set the task priority.
                // If the scheduler implements dynamic priority scheduling, the task priority will be updated later.
                let task_priority = match scheduler_type {
                    SchedulerType::PrioritizedFIFO(priority)
                    | SchedulerType::PrioritizedRR(priority) => priority as u64,
                    _ => MAX_TASK_PRIORITY,
                };

                let task = Task {
                    name,
                    future: Mutex::new(future),
                    scheduler,
                    id,
                    info,
                    priority: PriorityInfo::new(scheduler.priority(), task_priority),
                    partitioned_core,
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
/// let task_id = task::spawn("example task".into(), async { Ok(()) }, SchedulerType::PrioritizedFIFO(0));
/// ```
pub fn spawn(
    name: Cow<'static, str>,
    future: impl Future<Output = TaskResult> + 'static + Send,
    sched_type: SchedulerType,
) -> u32 {
    inner_spawn(name, future, sched_type, None)
}

/// Spawn a detached task with DAG information.
/// This function is similar to `spawn` but automatically sets DAG information
/// for the task, which is useful for DAG-based schedulers like GEDF.
///
/// # Example
///
/// ```ignore
/// use awkernel_async_lib::{scheduler::SchedulerType, task, dag::{create_dag, add_node_with_topic_edges_public, set_relative_deadline_public}};
/// use core::time::Duration;
/// let dag = create_dag();
/// let sink_node_idx = add_node_with_topic_edges_public(&dag, &[], &[]);
/// let deadline = Duration::from_millis(100);
/// set_relative_deadline_public(&dag, sink_node_idx, deadline);
/// let task_id = task::spawn_with_dag_info(
///     "dag task".into(),
///     async { Ok(()) },
///     SchedulerType::GEDF(0),
///     DagInfo { dag_id: 1, node_id: 0 }
/// );
/// ```
pub fn spawn_with_dag_info(
    name: Cow<'static, str>,
    future: impl Future<Output = TaskResult> + 'static + Send,
    sched_type: SchedulerType,
    dag_info: DagInfo,
) -> u32 {
    inner_spawn(name, future, sched_type, Some(dag_info))
}

pub fn inner_spawn(
    name: Cow<'static, str>,
    future: impl Future<Output = TaskResult> + 'static + Send,
    sched_type: SchedulerType,
    dag_info: Option<DagInfo>,
) -> u32 {
    if let SchedulerType::PrioritizedFIFO(p) | SchedulerType::PrioritizedRR(p) = sched_type {
        if p > HIGHEST_PRIORITY {
            log::warn!(
                "Task priority should be between 0 and {HIGHEST_PRIORITY}. It is addressed as {HIGHEST_PRIORITY}."
            );
        }
    }

    let future = future.boxed();

    let scheduler = get_scheduler(sched_type);

    let mut node = MCSNode::new();
    let mut tasks = TASKS.lock(&mut node);
    let id = tasks.spawn(name, future.fuse(), scheduler, sched_type, dag_info);
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
pub fn set_current_task(cpu_id: usize, task_id: u32) {
    RUNNING[cpu_id].store(task_id, Ordering::Relaxed);
}

#[inline(always)]
fn get_next_task(execution_ensured: bool) -> Option<Arc<Task>> {
    #[cfg(not(feature = "no_preempt"))]
    {
        if let Some(next) = preempt::get_next_task() {
            if execution_ensured {
                set_current_task(awkernel_lib::cpu::cpu_id(), next.id);
            }
            return Some(next);
        }
    }

    scheduler::get_next_task(execution_ensured)
}

#[cfg(feature = "perf")]
pub mod perf {
    use alloc::boxed::Box;
    use alloc::string::{String, ToString};
    use awkernel_lib::cpu::NUM_MAX_CPU;
    use core::ptr::{read_volatile, write_volatile};
    use core::sync::atomic::AtomicU32;

    #[derive(Debug, Clone, PartialEq, Eq)]
    #[repr(u8)]
    pub enum PerfState {
        Boot = 0,
        Kernel,
        Task,
        ContextSwitch,
        ContextSwitchMain,
        Interrupt,
        Idle,
    }

    impl From<u8> for PerfState {
        fn from(value: u8) -> Self {
            match value {
                0 => Self::Boot,
                1 => Self::Kernel,
                2 => Self::Task,
                3 => Self::ContextSwitch,
                4 => Self::ContextSwitchMain,
                5 => Self::Interrupt,
                6 => Self::Idle,
                _ => panic!("From<u8> for PerfState::from: invalid value"),
            }
        }
    }

    static mut PERF_STATES: [u8; NUM_MAX_CPU] = [0; NUM_MAX_CPU];

    static mut START_TIME: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];

    static mut KERNEL_TIME: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut TASK_TIME: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut INTERRUPT_TIME: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut CONTEXT_SWITCH_TIME: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut CONTEXT_SWITCH_MAIN_TIME: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut IDLE_TIME: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut PERF_TIME: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];

    static mut KERNEL_WCET: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut TASK_WCET: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut INTERRUPT_WCET: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut CONTEXT_SWITCH_WCET: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut CONTEXT_SWITCH_MAIN_WCET: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut IDLE_WCET: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut PERF_WCET: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];

    static mut KERNEL_COUNT: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut TASK_COUNT: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut INTERRUPT_COUNT: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut CONTEXT_SWITCH_COUNT: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut CONTEXT_SWITCH_MAIN_COUNT: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut IDLE_COUNT: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];
    static mut PERF_COUNT: [u64; NUM_MAX_CPU] = [0; NUM_MAX_CPU];

    use alloc::{collections::BTreeMap, vec::Vec};
    use awkernel_lib::sync::{mcs::MCSNode, mutex::Mutex};
    // NOTE: When logging evaluation results, this value can be adjusted based on awkernel's execution time.
    // This value matches the one actually used in the awkernel evaluation branch, and it is a ring buffer.
    const MAX_LOGS: usize = 8192;

    type DagTimestampMap = BTreeMap<u32, u64>;
    type DagTimestampTable = [DagTimestampMap; MAX_LOGS];

    static SEND_OUTER_TIMESTAMP: Mutex<Option<Box<DagTimestampTable>>> = Mutex::new(None);
    static RECV_OUTER_TIMESTAMP: Mutex<Option<Box<DagTimestampTable>>> = Mutex::new(None);
    static ABSOLUTE_DEADLINE: Mutex<Option<Box<DagTimestampTable>>> = Mutex::new(None);
    static RELATIVE_DEADLINE: Mutex<Option<Box<DagTimestampTable>>> = Mutex::new(None);

    pub static PERIOD_INDEX: Mutex<BTreeMap<u32, AtomicU32>> = Mutex::new(BTreeMap::new());

    pub fn get_period_index(dag_id: u32) -> u32 {
        let mut node = MCSNode::new();
        let period_count = PERIOD_INDEX.lock(&mut node);
        period_count
            .get(&dag_id)
            .map(|count| count.load(core::sync::atomic::Ordering::Relaxed))
            .unwrap_or(0)
    }

    pub fn increment_period_index(dag_id: u32) -> u32 {
        let mut node = MCSNode::new();
        let mut period_count = PERIOD_INDEX.lock(&mut node);
        let count = period_count
            .entry(dag_id)
            .or_insert_with(|| AtomicU32::new(0));
        count.fetch_add(1, core::sync::atomic::Ordering::Relaxed) + 1
    }
    // This value represents the type of pubsub (publish only, subscribe only, or both publish and subscribe)
    // and is a fixed value.
    const MAX_PUBSUB: usize = 3;
    // This value indicates the maximum number of nodes in the DAG
    // and can be adjusted based on the structure of the DAG used for evaluation.
    const MAX_NODES: usize = 5;

    type DagTimestamps = [[[u64; MAX_NODES]; MAX_PUBSUB]; MAX_LOGS];

    #[derive(Clone)]
    struct PubSubTable {
        by_dag: BTreeMap<u32, Box<DagTimestamps>>,
    }

    impl PubSubTable {
        fn new() -> Self {
            Self {
                by_dag: BTreeMap::new(),
            }
        }

        fn get_or_insert_dag(&mut self, dag_id: u32) -> &mut DagTimestamps {
            self.by_dag
                .entry(dag_id)
                .or_insert_with(|| Box::new([[[0u64; MAX_NODES]; MAX_PUBSUB]; MAX_LOGS]))
        }
    }

    static PUBLISH: Mutex<Option<Box<PubSubTable>>> = Mutex::new(None);
    static SUBSCRIBE: Mutex<Option<Box<PubSubTable>>> = Mutex::new(None);
    static SINK_EXEC_END: Mutex<Option<Box<PubSubTable>>> = Mutex::new(None);

    #[inline(always)]
    fn to_ring_buffer_index(period_index: usize) -> usize {
        period_index % MAX_LOGS
    }

    pub fn update_cycle_start_timestamp(period_index: usize, new_timestamp: u64, dag_id: u32) {
        let log_index = to_ring_buffer_index(period_index);

        let mut node = MCSNode::new();
        let mut recorder_opt = SEND_OUTER_TIMESTAMP.lock(&mut node);

        let recorder =
            recorder_opt.get_or_insert_with(|| Box::new(core::array::from_fn(|_| BTreeMap::new())));

        recorder[log_index].entry(dag_id).or_insert(new_timestamp);
    }

    pub fn update_cycle_end_timestamp(period_index: usize, new_timestamp: u64, dag_id: u32) {
        let log_index = to_ring_buffer_index(period_index);

        let mut node = MCSNode::new();
        let mut recorder_opt = RECV_OUTER_TIMESTAMP.lock(&mut node);

        let recorder =
            recorder_opt.get_or_insert_with(|| Box::new(core::array::from_fn(|_| BTreeMap::new())));

        recorder[log_index].insert(dag_id, new_timestamp);
    }

    pub fn update_absolute_deadline_timestamp(period_index: usize, deadline: u64, dag_id: u32) {
        let log_index = to_ring_buffer_index(period_index);

        let mut node = MCSNode::new();
        let mut recorder_opt = ABSOLUTE_DEADLINE.lock(&mut node);

        let recorder =
            recorder_opt.get_or_insert_with(|| Box::new(core::array::from_fn(|_| BTreeMap::new())));

        recorder[log_index].entry(dag_id).or_insert(deadline);
    }

    pub fn update_relative_deadline_timestamp(period_index: usize, deadline: u64, dag_id: u32) {
        let log_index = to_ring_buffer_index(period_index);

        let mut node = MCSNode::new();
        let mut recorder_opt = RELATIVE_DEADLINE.lock(&mut node);

        let recorder =
            recorder_opt.get_or_insert_with(|| Box::new(core::array::from_fn(|_| BTreeMap::new())));

        recorder[log_index].entry(dag_id).or_insert(deadline);
    }

    pub fn record_publish_timestamp(
        period_index: usize,
        new_timestamp: u64,
        pub_id: u32,
        node_id: u32,
        dag_id: u32,
    ) {
        let log_index = to_ring_buffer_index(period_index);
        if (pub_id as usize) >= MAX_PUBSUB {
            log::warn!(
                "Publish ID out of bounds: {} (max {})",
                pub_id as usize,
                MAX_PUBSUB
            );
            return;
        }

        let node_id_usize = node_id as usize;
        if node_id_usize >= MAX_NODES {
            log::warn!(
                "Publish node ID out of bounds: {} (max {})",
                node_id_usize,
                MAX_NODES
            );
            return;
        }

        let mut node = MCSNode::new();
        let mut recorder_opt = PUBLISH.lock(&mut node);

        let recorder = recorder_opt.get_or_insert_with(|| Box::new(PubSubTable::new()));
        let pub_id = pub_id as usize;
        let table = recorder.get_or_insert_dag(dag_id);

        if table[log_index][pub_id][node_id_usize] == 0 {
            table[log_index][pub_id][node_id_usize] = new_timestamp;
        }
    }

    pub fn record_subscribe_timestamp(
        period_index: usize,
        new_timestamp: u64,
        sub_id: u32,
        node_id: u32,
        dag_id: u32,
    ) {
        let log_index = to_ring_buffer_index(period_index);
        if (sub_id as usize) >= MAX_PUBSUB {
            log::warn!(
                "Subscribe ID out of bounds: {} (max {})",
                sub_id as usize,
                MAX_PUBSUB
            );
            return;
        }

        let node_id_usize = node_id as usize;
        if node_id_usize >= MAX_NODES {
            log::warn!(
                "Subscribe node ID out of bounds: {} (max {})",
                node_id_usize,
                MAX_NODES
            );
            return;
        }

        let mut node = MCSNode::new();
        let mut recorder_opt = SUBSCRIBE.lock(&mut node);

        let recorder = recorder_opt.get_or_insert_with(|| Box::new(PubSubTable::new()));
        let sub_id = sub_id as usize;
        let table = recorder.get_or_insert_dag(dag_id);

        if table[log_index][sub_id][node_id_usize] == 0 {
            table[log_index][sub_id][node_id_usize] = new_timestamp;
        }
    }

    pub fn record_sink_exec_end_timestamp(
        period_index: usize,
        new_timestamp: u64,
        node_id: u32,
        dag_id: u32,
    ) {
        let log_index = to_ring_buffer_index(period_index);

        let node_id_usize = node_id as usize;
        if node_id_usize >= MAX_NODES {
            log::warn!(
                "Sink exec-end node ID out of bounds: {} (max {})",
                node_id_usize,
                MAX_NODES
            );
            return;
        }

        let mut node = MCSNode::new();
        let mut recorder_opt = SINK_EXEC_END.lock(&mut node);

        let recorder = recorder_opt.get_or_insert_with(|| Box::new(PubSubTable::new()));
        let table = recorder.get_or_insert_dag(dag_id);

        if table[log_index][0][node_id_usize] == 0 {
            table[log_index][0][node_id_usize] = new_timestamp;
        }
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    pub enum DagNodeRole {
        Source,
        Middle,
        Sink,
    }

    pub struct DagNodeTimingSample {
        pub node_id: u32,
        pub role: DagNodeRole,
        /// exec time samples in nanoseconds per period
        pub exec_samples: Vec<u64>,
        /// comm time samples (from previous node) in nanoseconds per period
        pub comm_samples: Vec<u64>,
    }

    pub struct DagTimingStats {
        pub nodes: Vec<DagNodeTimingSample>,
        /// RECV_OUTER - SEND_OUTER per period (excludes sink exec)
        pub e2e_partial_samples: Vec<u64>,
    }

    fn get_or_insert_timing_node(
        nodes: &mut Vec<DagNodeTimingSample>,
        node_id: u32,
        role: DagNodeRole,
    ) -> &mut DagNodeTimingSample {
        if let Some(pos) = nodes.iter().position(|n| n.node_id == node_id) {
            &mut nodes[pos]
        } else {
            nodes.push(DagNodeTimingSample {
                node_id,
                role,
                exec_samples: Vec::new(),
                comm_samples: Vec::new(),
            });
            nodes.last_mut().unwrap()
        }
    }

    /// Scan all pubsub tables and compute per-DAG timing stats.
    ///
    /// Assumes a linear pipeline topology: source → (middle)* → sink.
    /// pub_id=0: source publish; sub_id=1: middle subscribe; pub_id=1: middle publish;
    /// sub_id=2: sink subscribe; SINK_EXEC_END: sink exec end.
    pub fn collect_all_dag_timing_stats() -> BTreeMap<u32, DagTimingStats> {
        let mut n1 = MCSNode::new();
        let mut n2 = MCSNode::new();
        let mut n3 = MCSNode::new();
        let mut n4 = MCSNode::new();
        let mut n5 = MCSNode::new();

        let send_outer_opt = SEND_OUTER_TIMESTAMP.lock(&mut n1);
        let recv_outer_opt = RECV_OUTER_TIMESTAMP.lock(&mut n2);
        let publish_opt = PUBLISH.lock(&mut n3);
        let subscribe_opt = SUBSCRIBE.lock(&mut n4);
        let sink_exec_end_opt = SINK_EXEC_END.lock(&mut n5);

        let mut dag_ids: Vec<u32> = Vec::new();
        if let Some(t) = publish_opt.as_ref() {
            dag_ids.extend(t.by_dag.keys().copied());
        }
        if let Some(t) = subscribe_opt.as_ref() {
            for k in t.by_dag.keys() {
                if !dag_ids.contains(k) {
                    dag_ids.push(*k);
                }
            }
        }
        dag_ids.sort_unstable();

        let mut result: BTreeMap<u32, DagTimingStats> = BTreeMap::new();

        for dag_id in dag_ids {
            let mut stats = DagTimingStats {
                nodes: Vec::new(),
                e2e_partial_samples: Vec::new(),
            };

            // Extract dag-specific table slices once before the period loop.
            // Using `match &*opt` (same pattern as print_timestamp_table) to avoid
            // lifetime issues with closures that return references via and_then.
            let pub_dag: Option<&DagTimestamps> = match &*publish_opt {
                Some(pt) => pt.by_dag.get(&dag_id).map(|b| b.as_ref()),
                None => None,
            };
            let sub_dag: Option<&DagTimestamps> = match &*subscribe_opt {
                Some(st) => st.by_dag.get(&dag_id).map(|b| b.as_ref()),
                None => None,
            };
            let sink_dag: Option<&DagTimestamps> = match &*sink_exec_end_opt {
                Some(se) => se.by_dag.get(&dag_id).map(|b| b.as_ref()),
                None => None,
            };

            for p in 0..MAX_LOGS {
                let send_outer = match &*send_outer_opt {
                    Some(arr) => arr[p].get(&dag_id).copied().unwrap_or(0),
                    None => 0,
                };
                let recv_outer = match &*recv_outer_opt {
                    Some(arr) => arr[p].get(&dag_id).copied().unwrap_or(0),
                    None => 0,
                };

                if send_outer != 0 && recv_outer != 0 && recv_outer > send_outer {
                    stats.e2e_partial_samples.push(recv_outer - send_outer);
                }

                // source pub (pub_id=0)
                let mut src_pub_ts = 0u64;
                let mut src_node_id = 0u32;
                if let Some(t) = pub_dag {
                    for k in 0..MAX_NODES {
                        if t[p][0][k] != 0 {
                            src_pub_ts = t[p][0][k];
                            src_node_id = k as u32;
                            break;
                        }
                    }
                }
                if src_pub_ts != 0 && send_outer != 0 && src_pub_ts > send_outer {
                    get_or_insert_timing_node(&mut stats.nodes, src_node_id, DagNodeRole::Source)
                        .exec_samples
                        .push(src_pub_ts - send_outer);
                }

                // Collect ALL middle nodes (slot [1]).
                // All spawn_reactor nodes use sub_id=1 / pub_id=1 regardless of chain position.
                // Sort by subscribe time to reconstruct linear chain order, then compute
                // comm (from predecessor pub) and exec (pub - sub) for each node.
                let mut mid_nodes: Vec<(u64, u64, u32)> = Vec::new(); // (sub_ts, pub_ts, node_id)
                for k in 0..MAX_NODES {
                    let sub_ts = sub_dag.map(|t| t[p][1][k]).unwrap_or(0);
                    let pub_ts = pub_dag.map(|t| t[p][1][k]).unwrap_or(0);
                    if sub_ts != 0 || pub_ts != 0 {
                        mid_nodes.push((sub_ts, pub_ts, k as u32));
                    }
                }
                mid_nodes.sort_by_key(|&(sub_ts, _, _)| sub_ts);

                let mut prev_pub_ts = src_pub_ts;
                for &(mid_sub_ts, mid_pub_ts, mid_node_id) in &mid_nodes {
                    if prev_pub_ts != 0 && mid_sub_ts != 0 && mid_sub_ts > prev_pub_ts {
                        get_or_insert_timing_node(
                            &mut stats.nodes,
                            mid_node_id,
                            DagNodeRole::Middle,
                        )
                        .comm_samples
                        .push(mid_sub_ts - prev_pub_ts);
                    }
                    if mid_sub_ts != 0 && mid_pub_ts != 0 && mid_pub_ts > mid_sub_ts {
                        get_or_insert_timing_node(
                            &mut stats.nodes,
                            mid_node_id,
                            DagNodeRole::Middle,
                        )
                        .exec_samples
                        .push(mid_pub_ts - mid_sub_ts);
                    }
                    if mid_pub_ts != 0 {
                        prev_pub_ts = mid_pub_ts;
                    }
                }

                // sink sub (sub_id=2)
                let last_mid_pub_ts = mid_nodes
                    .last()
                    .map(|&(_, pub_ts, _)| pub_ts)
                    .unwrap_or(src_pub_ts);
                let mut sink_sub_ts = 0u64;
                let mut sink_node_id = 0u32;
                if let Some(t) = sub_dag {
                    for k in 0..MAX_NODES {
                        if t[p][2][k] != 0 {
                            sink_sub_ts = t[p][2][k];
                            sink_node_id = k as u32;
                            break;
                        }
                    }
                }
                if last_mid_pub_ts != 0 && sink_sub_ts != 0 && sink_sub_ts > last_mid_pub_ts {
                    get_or_insert_timing_node(&mut stats.nodes, sink_node_id, DagNodeRole::Sink)
                        .comm_samples
                        .push(sink_sub_ts - last_mid_pub_ts);
                }

                // sink exec end (index 0 in SINK_EXEC_END)
                let mut sink_exec_end_ts = 0u64;
                if let Some(t) = sink_dag {
                    for k in 0..MAX_NODES {
                        if t[p][0][k] != 0 {
                            sink_exec_end_ts = t[p][0][k];
                            break;
                        }
                    }
                }
                if sink_sub_ts != 0 && sink_exec_end_ts != 0 && sink_exec_end_ts > sink_sub_ts {
                    get_or_insert_timing_node(&mut stats.nodes, sink_node_id, DagNodeRole::Sink)
                        .exec_samples
                        .push(sink_exec_end_ts - sink_sub_ts);
                }
            }

            stats.nodes.sort_by_key(|n| n.node_id);
            result.insert(dag_id, stats);
        }

        result
    }

    // For precision of the cycle
    pub fn print_timestamp_table() {
        let mut node1 = MCSNode::new();
        let mut node2 = MCSNode::new();
        let mut node3 = MCSNode::new();
        let mut node4 = MCSNode::new();
        const MAX_ROWS_TO_PRINT: usize = 256;

        let send_outer_opt = SEND_OUTER_TIMESTAMP.lock(&mut node1);
        let recv_outer_opt = RECV_OUTER_TIMESTAMP.lock(&mut node2);
        let absolute_deadline_opt = ABSOLUTE_DEADLINE.lock(&mut node3);
        let relative_deadline_opt = RELATIVE_DEADLINE.lock(&mut node4);

        let mut rows = Vec::new();
        let mut truncated = false;
        'collect_rows: for i in 0..MAX_LOGS {
            let mut dag_ids = Vec::new();
            if let Some(arr) = &*send_outer_opt {
                dag_ids.extend(arr[i].keys().copied());
            }
            if let Some(arr) = &*recv_outer_opt {
                dag_ids.extend(arr[i].keys().copied());
            }
            if let Some(arr) = &*absolute_deadline_opt {
                dag_ids.extend(arr[i].keys().copied());
            }
            if let Some(arr) = &*relative_deadline_opt {
                dag_ids.extend(arr[i].keys().copied());
            }

            dag_ids.sort_unstable();
            dag_ids.dedup();

            for dag_id in dag_ids {
                let pre_send_outer = match &*send_outer_opt {
                    Some(arr) => arr[i].get(&dag_id).copied().unwrap_or(0),
                    None => 0,
                };
                let fin_recv_outer = match &*recv_outer_opt {
                    Some(arr) => arr[i].get(&dag_id).copied().unwrap_or(0),
                    None => 0,
                };
                let absolute_deadline = match &*absolute_deadline_opt {
                    Some(arr) => arr[i].get(&dag_id).copied().unwrap_or(0),
                    None => 0,
                };
                let relative_deadline = match &*relative_deadline_opt {
                    Some(arr) => arr[i].get(&dag_id).copied().unwrap_or(0),
                    None => 0,
                };

                if pre_send_outer != 0
                    || fin_recv_outer != 0
                    || absolute_deadline != 0
                    || relative_deadline != 0
                {
                    if rows.len() >= MAX_ROWS_TO_PRINT {
                        truncated = true;
                        break 'collect_rows;
                    }
                    rows.push((
                        i,
                        dag_id,
                        pre_send_outer,
                        fin_recv_outer,
                        absolute_deadline,
                        relative_deadline,
                    ));
                }
            }
        }
        drop(relative_deadline_opt);
        drop(absolute_deadline_opt);
        drop(recv_outer_opt);
        drop(send_outer_opt);

        log::info!("--- Timestamp Summary (in nanoseconds) ---");
        log::info!(
            "{: ^5} | {: ^5} | {: ^14} | {: ^14} | {: ^14} | {: ^14} | {: ^14}",
            "Index",
            "DAG-ID",
            "Send-Outer",
            "Recv-Outer",
            "Latency",
            "Absolute Deadline",
            "Relative Deadline"
        );

        log::info!("-----|--------|----------------|----------------|----------------|--------------------|--------------------");

        for (i, dag_id, pre_send_outer, fin_recv_outer, absolute_deadline, relative_deadline) in
            rows
        {
            let format_ts = |ts: u64| -> String {
                if ts == 0 {
                    "-".to_string()
                } else {
                    ts.to_string()
                }
            };

            let latency_str = if pre_send_outer != 0 && fin_recv_outer != 0 {
                fin_recv_outer.saturating_sub(pre_send_outer).to_string()
            } else {
                "-".to_string()
            };

            log::info!(
                "{: >5} | {: >5} | {: >14} | {: >14} | {: >14} | {: >20} | {: >20}",
                i,
                format_ts(dag_id as u64),
                format_ts(pre_send_outer),
                format_ts(fin_recv_outer),
                latency_str,
                format_ts(absolute_deadline),
                format_ts(relative_deadline),
            );
        }
        if truncated {
            log::warn!(
                "Timestamp Summary truncated to {} rows; call print_timestamp_table() again to continue inspection",
                MAX_ROWS_TO_PRINT
            );
        }
        log::info!("----------------------------------------------------------");
    }

    // For pubsub communication latency
    pub fn print_pubsub_table() {
        let mut node1 = MCSNode::new();
        let mut node2 = MCSNode::new();

        let publish_opt = PUBLISH.lock(&mut node1);
        let subscribe_opt = SUBSCRIBE.lock(&mut node2);

        let mut dag_ids: Vec<u32> = Vec::new();
        if let Some(t) = publish_opt.as_ref() {
            dag_ids.extend(t.by_dag.keys().copied());
        }
        if let Some(t) = subscribe_opt.as_ref() {
            for k in t.by_dag.keys() {
                if !dag_ids.contains(k) {
                    dag_ids.push(*k);
                }
            }
        }
        dag_ids.sort_unstable();

        log::info!("--- Pub/Sub Timestamp Summary (in nanoseconds) ---");
        log::info!(
            "{: ^6} | {: ^5} | {: ^10} | {: ^7} | {: ^14} | {: ^14}",
            "DAG-ID",
            "Index",
            "Pub/Sub ID",
            "Node ID",
            "Publish Time",
            "Subscribe Time"
        );
        log::info!("--------|-------|------------|---------|----------------|----------------");

        let format_ts = |ts: u64| -> String {
            if ts == 0 {
                "-".to_string()
            } else {
                ts.to_string()
            }
        };

        for dag_id in &dag_ids {
            for i in 0..MAX_LOGS {
                for j in 0..MAX_PUBSUB {
                    for k in 0..MAX_NODES {
                        let pub_time = match &*publish_opt {
                            Some(pt) => pt.by_dag.get(dag_id).map(|ts| ts[i][j][k]).unwrap_or(0),
                            None => 0,
                        };
                        let sub_time = match &*subscribe_opt {
                            Some(st) => st.by_dag.get(dag_id).map(|ts| ts[i][j][k]).unwrap_or(0),
                            None => 0,
                        };

                        if pub_time != 0 || sub_time != 0 {
                            log::info!(
                                "{: >6} | {: >5} | {: >10} | {: >7} | {: >14} | {: >14}",
                                dag_id,
                                i,
                                j,
                                k,
                                format_ts(pub_time),
                                format_ts(sub_time),
                            );
                        }
                    }
                }
            }
        }
        log::info!("--------------------------------------------------------------");
    }

    fn update_time_and_state(next_state: PerfState) {
        let end = awkernel_lib::delay::cpu_counter();
        let cpu_id = awkernel_lib::cpu::cpu_id();

        let state: PerfState = unsafe { read_volatile(&PERF_STATES[cpu_id]) }.into();
        if state == next_state {
            return;
        }

        let start = unsafe { read_volatile(&START_TIME[cpu_id]) };

        if start > 0 && start <= end {
            let diff = end - start;

            match state {
                PerfState::Kernel => unsafe {
                    let t = read_volatile(&KERNEL_TIME[cpu_id]);
                    write_volatile(&mut KERNEL_TIME[cpu_id], t + diff);
                    let c = read_volatile(&KERNEL_COUNT[cpu_id]);
                    write_volatile(&mut KERNEL_COUNT[cpu_id], c + 1);
                    let wcet = read_volatile(&KERNEL_WCET[cpu_id]);
                    write_volatile(&mut KERNEL_WCET[cpu_id], wcet.max(diff));
                },
                PerfState::Task => unsafe {
                    let t = read_volatile(&TASK_TIME[cpu_id]);
                    write_volatile(&mut TASK_TIME[cpu_id], t + diff);
                    let c = read_volatile(&TASK_COUNT[cpu_id]);
                    write_volatile(&mut TASK_COUNT[cpu_id], c + 1);
                    let wcet = read_volatile(&TASK_WCET[cpu_id]);
                    write_volatile(&mut TASK_WCET[cpu_id], wcet.max(diff));
                },
                PerfState::Interrupt => unsafe {
                    let t = read_volatile(&INTERRUPT_TIME[cpu_id]);
                    write_volatile(&mut INTERRUPT_TIME[cpu_id], t + diff);
                    let c = read_volatile(&INTERRUPT_COUNT[cpu_id]);
                    write_volatile(&mut INTERRUPT_COUNT[cpu_id], c + 1);
                    let wcet = read_volatile(&INTERRUPT_WCET[cpu_id]);
                    write_volatile(&mut INTERRUPT_WCET[cpu_id], wcet.max(diff));
                },
                PerfState::ContextSwitch => unsafe {
                    let t = read_volatile(&CONTEXT_SWITCH_TIME[cpu_id]);
                    write_volatile(&mut CONTEXT_SWITCH_TIME[cpu_id], t + diff);
                    let c = read_volatile(&CONTEXT_SWITCH_COUNT[cpu_id]);
                    write_volatile(&mut CONTEXT_SWITCH_COUNT[cpu_id], c + 1);
                    let wcet = read_volatile(&CONTEXT_SWITCH_WCET[cpu_id]);
                    write_volatile(&mut CONTEXT_SWITCH_WCET[cpu_id], wcet.max(diff));
                },
                PerfState::ContextSwitchMain => unsafe {
                    let t = read_volatile(&CONTEXT_SWITCH_MAIN_TIME[cpu_id]);
                    write_volatile(&mut CONTEXT_SWITCH_MAIN_TIME[cpu_id], t + diff);
                    let c = read_volatile(&CONTEXT_SWITCH_MAIN_COUNT[cpu_id]);
                    write_volatile(&mut CONTEXT_SWITCH_MAIN_COUNT[cpu_id], c + 1);
                    let wcet = read_volatile(&CONTEXT_SWITCH_MAIN_WCET[cpu_id]);
                    write_volatile(&mut CONTEXT_SWITCH_MAIN_WCET[cpu_id], wcet.max(diff));
                },
                PerfState::Idle => unsafe {
                    let t = read_volatile(&IDLE_TIME[cpu_id]);
                    write_volatile(&mut IDLE_TIME[cpu_id], t + diff);
                    let c = read_volatile(&IDLE_COUNT[cpu_id]);
                    write_volatile(&mut IDLE_COUNT[cpu_id], c + 1);
                    let wcet = read_volatile(&IDLE_WCET[cpu_id]);
                    write_volatile(&mut IDLE_WCET[cpu_id], wcet.max(diff));
                },
                PerfState::Boot => (),
            }
        }

        let cnt = awkernel_lib::delay::cpu_counter();

        unsafe {
            // Overhead of this.
            let t = read_volatile(&PERF_TIME[cpu_id]);
            write_volatile(&mut PERF_TIME[cpu_id], t + (cnt - end));
            let c = read_volatile(&PERF_COUNT[cpu_id]);
            write_volatile(&mut PERF_COUNT[cpu_id], c + 1);
            let wcet = read_volatile(&PERF_WCET[cpu_id]);
            write_volatile(&mut PERF_WCET[cpu_id], wcet.max(cnt - end));

            // State transition.
            write_volatile(&mut START_TIME[cpu_id], cnt);
            write_volatile(&mut PERF_STATES[cpu_id], next_state as u8);
        }
    }

    #[inline(always)]
    pub fn start_kernel() {
        update_time_and_state(PerfState::Kernel);
    }

    #[inline(always)]
    pub(crate) fn start_task() {
        update_time_and_state(PerfState::Task);
    }

    /// Return the previous state.
    #[inline(always)]
    pub fn start_interrupt() -> PerfState {
        let cpu_id = awkernel_lib::cpu::cpu_id();
        let previous: PerfState = unsafe { read_volatile(&PERF_STATES[cpu_id]) }.into();
        update_time_and_state(PerfState::Interrupt);
        previous
    }

    #[inline(always)]
    pub fn transition_to(next: PerfState) {
        match next {
            PerfState::Boot => unreachable!(),
            PerfState::Kernel => start_kernel(),
            PerfState::Task => start_task(),
            PerfState::ContextSwitch => start_context_switch(),
            PerfState::ContextSwitchMain => start_context_switch_main(),
            PerfState::Interrupt => {
                start_interrupt();
            }
            PerfState::Idle => start_idle(),
        }
    }

    #[inline(always)]
    pub(crate) fn start_context_switch() {
        update_time_and_state(PerfState::ContextSwitch);
    }

    #[inline(always)]
    pub(crate) fn start_context_switch_main() {
        update_time_and_state(PerfState::ContextSwitchMain);
    }

    #[inline(always)]
    pub fn start_idle() {
        update_time_and_state(PerfState::Idle);
    }

    #[inline(always)]
    pub fn get_kernel_time(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&KERNEL_TIME[cpu_id]) }
    }

    #[inline(always)]
    pub fn get_task_time(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&TASK_TIME[cpu_id]) }
    }

    #[inline(always)]
    pub fn get_interrupt_time(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&INTERRUPT_TIME[cpu_id]) }
    }

    #[inline(always)]
    pub fn get_context_switch_time(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&CONTEXT_SWITCH_TIME[cpu_id]) }
    }

    #[inline(always)]
    pub fn get_idle_time(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&IDLE_TIME[cpu_id]) }
    }

    #[inline(always)]
    pub fn get_perf_time(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&PERF_TIME[cpu_id]) }
    }

    #[inline(always)]
    pub fn get_ave_kernel_time(cpu_id: usize) -> Option<f64> {
        let total = get_kernel_time(cpu_id);
        let count = unsafe { read_volatile(&KERNEL_COUNT[cpu_id]) };
        (count != 0).then_some((total as f64) / (count as f64))
    }

    #[inline(always)]
    pub fn get_ave_task_time(cpu_id: usize) -> Option<f64> {
        let total = get_task_time(cpu_id);
        let count = unsafe { read_volatile(&TASK_COUNT[cpu_id]) };
        (count != 0).then_some((total as f64) / (count as f64))
    }

    #[inline(always)]
    pub fn get_ave_interrupt_time(cpu_id: usize) -> Option<f64> {
        let total = get_interrupt_time(cpu_id);
        let count = unsafe { read_volatile(&INTERRUPT_COUNT[cpu_id]) };
        (count != 0).then_some((total as f64) / (count as f64))
    }

    #[inline(always)]
    pub fn get_ave_context_switch_time(cpu_id: usize) -> Option<f64> {
        let total = get_context_switch_time(cpu_id);
        let count = unsafe { read_volatile(&CONTEXT_SWITCH_COUNT[cpu_id]) };
        (count != 0).then_some((total as f64) / (count as f64))
    }

    #[inline(always)]
    pub fn get_ave_idle_time(cpu_id: usize) -> Option<f64> {
        let total = get_idle_time(cpu_id);
        let count = unsafe { read_volatile(&IDLE_COUNT[cpu_id]) };
        (count != 0).then_some((total as f64) / (count as f64))
    }

    #[inline(always)]
    pub fn get_ave_perf_time(cpu_id: usize) -> Option<f64> {
        let total = get_perf_time(cpu_id);
        let count = unsafe { read_volatile(&PERF_COUNT[cpu_id]) };
        (count != 0).then_some((total as f64) / (count as f64))
    }

    #[inline(always)]
    pub fn get_kernel_wcet(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&KERNEL_WCET[cpu_id]) }
    }
    #[inline(always)]
    pub fn get_task_wcet(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&TASK_WCET[cpu_id]) }
    }
    #[inline(always)]
    pub fn get_idle_wcet(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&IDLE_WCET[cpu_id]) }
    }
    #[inline(always)]
    pub fn get_interrupt_wcet(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&INTERRUPT_WCET[cpu_id]) }
    }
    #[inline(always)]
    pub fn get_context_switch_wcet(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&CONTEXT_SWITCH_WCET[cpu_id]) }
    }
    #[inline(always)]
    pub fn get_perf_wcet(cpu_id: usize) -> u64 {
        unsafe { read_volatile(&PERF_WCET[cpu_id]) }
    }

    // ─── DAG aggregate statistics ────────────────────────────────────────────

    #[cfg(feature = "period-index-propagation")]
    fn samples_avg(s: &[u64]) -> Option<u64> {
        if s.is_empty() {
            None
        } else {
            Some(s.iter().sum::<u64>() / s.len() as u64)
        }
    }

    #[cfg(feature = "period-index-propagation")]
    fn samples_wcet(s: &[u64]) -> Option<u64> {
        s.iter().copied().reduce(u64::max)
    }

    #[cfg(feature = "period-index-propagation")]
    pub struct DagNodeStats {
        pub node_id: u32,
        pub role: DagNodeRole,
        pub exec_avg: Option<u64>,
        pub exec_wcet: Option<u64>,
        pub comm_avg: Option<u64>,
        pub comm_wcet: Option<u64>,
    }

    #[cfg(feature = "period-index-propagation")]
    pub struct DagStats {
        pub dag_id: u32,
        pub cores: Vec<u16>,
        pub total_preempts: u64,
        pub exec_avg: u64,
        pub exec_wcet: u64,
        pub comm_avg: u64,
        pub comm_wcet: u64,
        pub e2e_partial_avg: Option<u64>,
        pub e2e_partial_wcet: Option<u64>,
        pub period_count: u32,
        pub nodes: Vec<DagNodeStats>,
    }

    /// Aggregate pubsub timestamps and task metadata into per-DAG statistics.
    #[cfg(feature = "period-index-propagation")]
    pub fn get_all_dag_stats() -> Vec<DagStats> {
        let timing_map = collect_all_dag_timing_stats();
        let all_tasks = super::get_tasks();

        let mut result = Vec::new();

        for (dag_id, timing) in &timing_map {
            let mut cores: Vec<u16> = Vec::new();
            let mut total_preempts: u64 = 0;

            for t in &all_tasks {
                let mut node = MCSNode::new();
                let info = t.info.lock(&mut node);
                if let Some(di) = info.get_dag_info() {
                    if di.dag_id == *dag_id {
                        total_preempts += info.get_num_preemption();
                        if let Some(core) = t.partitioned_core {
                            if !cores.contains(&core) {
                                cores.push(core);
                            }
                        }
                    }
                }
            }
            cores.sort_unstable();

            let mut nodes = Vec::new();
            let mut exec_avg_sum: u64 = 0;
            let mut exec_wcet_max: u64 = 0;
            let mut comm_avg_sum: u64 = 0;
            let mut comm_wcet_max: u64 = 0;

            for nt in &timing.nodes {
                let ea = samples_avg(&nt.exec_samples);
                let ew = samples_wcet(&nt.exec_samples);
                let ca = samples_avg(&nt.comm_samples);
                let cw = samples_wcet(&nt.comm_samples);
                exec_avg_sum += ea.unwrap_or(0);
                exec_wcet_max = exec_wcet_max.max(ew.unwrap_or(0));
                comm_avg_sum += ca.unwrap_or(0);
                comm_wcet_max = comm_wcet_max.max(cw.unwrap_or(0));
                nodes.push(DagNodeStats {
                    node_id: nt.node_id,
                    role: nt.role,
                    exec_avg: ea,
                    exec_wcet: ew,
                    comm_avg: ca,
                    comm_wcet: cw,
                });
            }

            result.push(DagStats {
                dag_id: *dag_id,
                cores,
                total_preempts,
                exec_avg: exec_avg_sum,
                exec_wcet: exec_wcet_max,
                comm_avg: comm_avg_sum,
                comm_wcet: comm_wcet_max,
                e2e_partial_avg: samples_avg(&timing.e2e_partial_samples),
                e2e_partial_wcet: samples_wcet(&timing.e2e_partial_samples),
                period_count: timing.e2e_partial_samples.len() as u32,
                nodes,
            });
        }

        result
    }

    #[cfg(feature = "period-index-propagation")]
    pub fn print_dag_table() {
        use alloc::format;
        let stats = get_all_dag_stats();
        if stats.is_empty() {
            return;
        }

        log::info!("--- DAG Statistics (ns) ---");
        log::info!(
            "{:>4} | {:>9} | {:>7} | {:>9} | {:>9} | {:>9} | {:>9} | {:>9} | {:>9}",
            "DAG",
            "#preempt",
            "periods",
            "exec_avg",
            "exec_wc",
            "comm_avg",
            "comm_wc",
            "e2e_avg",
            "e2e_wc"
        );
        log::info!("-----|-----------|---------|-----------|-----------|-----------|-----------|-----------|----------");

        for dag in &stats {
            let e2e_avg = dag
                .e2e_partial_avg
                .map(|v| format!("{}", v))
                .unwrap_or_else(|| "-".into());
            let e2e_wcet = dag
                .e2e_partial_wcet
                .map(|v| format!("{}", v))
                .unwrap_or_else(|| "-".into());
            log::info!(
                "{:>4} | {:>9} | {:>7} | {:>9} | {:>9} | {:>9} | {:>9} | {:>9} | {:>9}",
                dag.dag_id,
                dag.total_preempts,
                dag.period_count,
                dag.exec_avg,
                dag.exec_wcet,
                dag.comm_avg,
                dag.comm_wcet,
                e2e_avg,
                e2e_wcet,
            );
        }

        for dag in &stats {
            log::info!("DAG {} node detail:", dag.dag_id);
            log::info!(
                "{:>5} | {:6} | {:>9} | {:>9} | {:>9} | {:>9}",
                "node",
                "role",
                "exec_avg",
                "exec_wc",
                "comm_avg",
                "comm_wc"
            );
            for n in &dag.nodes {
                let role_str = match n.role {
                    DagNodeRole::Source => "src   ",
                    DagNodeRole::Middle => "middle",
                    DagNodeRole::Sink => "sink  ",
                };
                let ea = n
                    .exec_avg
                    .map(|v| format!("{}", v))
                    .unwrap_or_else(|| "-".into());
                let ew = n
                    .exec_wcet
                    .map(|v| format!("{}", v))
                    .unwrap_or_else(|| "-".into());
                let ca = n
                    .comm_avg
                    .map(|v| format!("{}", v))
                    .unwrap_or_else(|| "-".into());
                let cw = n
                    .comm_wcet
                    .map(|v| format!("{}", v))
                    .unwrap_or_else(|| "-".into());
                log::info!(
                    "{:>5} | {} | {:>9} | {:>9} | {:>9} | {:>9}",
                    n.node_id,
                    role_str,
                    ea,
                    ew,
                    ca,
                    cw
                );
            }
        }
    }
}

pub fn run_main() {
    loop {
        #[cfg(feature = "perf")]
        perf::start_kernel();

        let cpu_id = awkernel_lib::cpu::cpu_id();
        if RUNNING[cpu_id].load(Ordering::Relaxed) == 0 {
            // Re-wake all preemption-pending tasks, because the preemption is no longer required.
            while let Some(p) = pop_preemption_pending(cpu_id) {
                p.scheduler.wake_task(p);
            }
        }

        if let Some(task) = get_next_task(true) {
            PREEMPTION_REQUEST[cpu_id].store(false, Ordering::Relaxed);

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
                    perf::start_context_switch();

                    unsafe { preempt::yield_and_pool(ctx) };

                    #[cfg(feature = "perf")]
                    perf::start_kernel();

                    continue;
                }
            }

            let w = waker_ref(&task);
            let mut ctx = Context::from_waker(&w);

            let result = {
                let cpu_id = awkernel_lib::cpu::cpu_id();
                let mut node = MCSNode::new();
                let Some(mut guard) = task.future.try_lock(&mut node) else {
                    // This task is running on another CPU,
                    // and re-schedule the task to avoid starvation just in case.
                    RUNNING[cpu_id].store(0, Ordering::Relaxed);
                    task.wake();
                    continue;
                };

                // Can remove this?
                if guard.is_terminated() {
                    RUNNING[cpu_id].store(0, Ordering::Relaxed);
                    continue;
                }

                {
                    let mut node = MCSNode::new();
                    let mut info = task.info.lock(&mut node);

                    if matches!(info.state, State::Terminated | State::Panicked) {
                        RUNNING[cpu_id].store(0, Ordering::Relaxed);
                        continue;
                    }

                    info.update_last_executed();
                }

                // Use the primary memory allocator.
                #[cfg(not(feature = "std"))]
                unsafe {
                    awkernel_lib::heap::TALLOC.use_primary_cpu_id(cpu_id)
                };

                // This is unnecessary if the task is scheduled by PrioritizedFIFO. This remains for other schedulers.
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

                    #[cfg(feature = "perf")]
                    perf::start_task();

                    #[allow(clippy::let_and_return)]
                    let result = guard.poll_unpin(&mut ctx);

                    #[cfg(feature = "perf")]
                    perf::start_kernel();

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
                Err(_) => {
                    // Caught panic.
                    info.state = State::Panicked;
                    drop(info);

                    let mut node = MCSNode::new();
                    let mut tasks = TASKS.lock(&mut node);

                    tasks.remove(task.id);
                }
            }
        } else {
            #[cfg(feature = "perf")]
            perf::start_idle();

            awkernel_lib::cpu::sleep_cpu(None);
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

    for task in tasks.id_to_task.values() {
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

/// Get the running task for the given CPU.
///
/// `cpu_id` must be less than `awkernel_lib::cpu::num_cpu()`.
/// The returned [`RunningTask::task_id`] is `0` when the CPU is idle.
///
/// To get the running tasks for all CPUs at once, use [`get_tasks_running`].
pub fn get_task_running(cpu_id: usize) -> RunningTask {
    let task_id = RUNNING[cpu_id].load(Ordering::Relaxed);
    RunningTask { cpu_id, task_id }
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
pub fn get_task(task_id: u32) -> Option<Arc<Task>> {
    let mut node = MCSNode::new();
    let tasks = TASKS.lock(&mut node);
    tasks.id_to_task.get(&task_id).cloned()
}

#[inline(always)]
pub fn get_last_executed_by_task_id(task_id: u32) -> Option<awkernel_lib::time::Time> {
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
pub fn set_need_preemption(task_id: u32, cpu_id: usize) {
    let mut node = MCSNode::new();
    let tasks = TASKS.lock(&mut node);

    if let Some(task) = tasks.id_to_task.get(&task_id) {
        let mut node = MCSNode::new();
        let mut info = task.info.lock(&mut node);
        info.need_preemption = true;
    }

    PREEMPTION_REQUEST[cpu_id].store(true, Ordering::Release);
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
    #[cfg(target_pointer_width = "64")]
    pub priority: AtomicU64,

    #[cfg(target_pointer_width = "32")]
    pub priority: AtomicU32,
}

impl PriorityInfo {
    fn new(scheduler_priority: u8, task_priority: u64) -> Self {
        PriorityInfo {
            #[cfg(target_pointer_width = "64")]
            priority: AtomicU64::new(Self::combine_priority(scheduler_priority, task_priority)),

            #[cfg(target_pointer_width = "32")]
            priority: AtomicU32::new(Self::combine_priority(scheduler_priority, task_priority)),
        }
    }

    #[cfg(target_pointer_width = "64")]
    pub fn update_priority_info(&self, scheduler_priority: u8, task_priority: u64) {
        self.priority.store(
            Self::combine_priority(scheduler_priority, task_priority),
            Ordering::Relaxed,
        );
    }

    #[cfg(target_pointer_width = "32")]
    pub fn update_priority_info(&self, scheduler_priority: u8, task_priority: u64) {
        self.priority.store(
            Self::combine_priority(scheduler_priority, task_priority),
            Ordering::Relaxed,
        );
    }

    #[cfg(target_pointer_width = "64")]
    fn combine_priority(scheduler_priority: u8, task_priority: u64) -> u64 {
        assert!(task_priority < (1 << 56), "Task priority exceeds 56 bits");
        ((scheduler_priority as u64) << 56) | (task_priority & ((1 << 56) - 1))
    }

    #[cfg(target_pointer_width = "32")]
    fn combine_priority(scheduler_priority: u8, task_priority: u64) -> u32 {
        let task_priority_32 = task_priority as u32;
        assert!(
            task_priority_32 < (1 << 24),
            "Task priority exceeds 24 bits for 32-bit"
        );
        ((scheduler_priority as u32) << 24) | (task_priority_32 & ((1 << 24) - 1))
    }
}

impl Clone for PriorityInfo {
    fn clone(&self) -> Self {
        let value = self.priority.load(Ordering::Relaxed);
        PriorityInfo {
            #[cfg(target_pointer_width = "64")]
            priority: AtomicU64::new(value),

            #[cfg(target_pointer_width = "32")]
            priority: AtomicU32::new(value),
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

/// Wake workers up.
pub fn wake_workers() {
    let num_cpus = awkernel_lib::cpu::num_cpu();
    let mut num_tasks = NUM_TASK_IN_QUEUE.load(Ordering::Relaxed);

    for (i, partitioned_tasks) in NUM_PARTITIONED_TASKS_IN_QUEUE[..num_cpus]
        .iter()
        .enumerate()
        .skip(1)
    {
        if (*partitioned_tasks).load(Ordering::Relaxed) > 0 {
            awkernel_lib::cpu::wake_cpu(i);
            continue;
        }

        if num_tasks == 0 {
            break;
        }

        if awkernel_lib::cpu::wake_cpu(i) {
            num_tasks -= 1;
        }
    }
}
