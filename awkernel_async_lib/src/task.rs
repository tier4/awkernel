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
    cpu::NUM_MAX_CPU,
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
pub(crate) static NUM_TASK_IN_QUEUE: AtomicU64 = AtomicU64::new(0); // Number of tasks in the queue.

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
                    // Runnable --> push start
                    // use crate::task::perf::{NodeRecord, node_start};
                    // let start = awkernel_lib::time::Time::now().uptime().as_nanos() as u64;
                    // {
                    //     let dag_info = info.get_dag_info();
                    //     if dag_info.is_some() {
                    //         // DAG task-specific handling
                    //         {
                    //             let period = info.get_current_period().unwrap_or(0);
                    //             if period != 0{
                    //                 if let Some(di) = dag_info {
                    //                     let nr = NodeRecord {
                    //                         period_count: period,
                    //                         dag_info: DagInfo { dag_id: di.dag_id, node_id: di.node_id },
                    //                     };
                    //                     node_start(nr, start);
                    //                 }
                    //             }
                    //         }
                    //     }
                    // }
                }
            }

            panicked = info.panicked;
        }

        NUM_TASK_IN_QUEUE.fetch_add(1, Ordering::Release);

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
    pub(crate) absolute_deadline: Option<u64>,
    need_sched: bool,
    pub(crate) need_preemption: bool,
    panicked: bool,
    pub(crate) dag_info: Option<DagInfo>,
    // latest period observed for this task (from received message payload), if any
    pub(crate) current_period: Option<u32>,
    pub(crate) need_terminate: bool,

    #[cfg(not(feature = "no_preempt"))]
    thread: Option<PtrWorkerThreadContext>,

    pub(crate) release_time: Option<awkernel_lib::time::Time>,
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

    #[inline(always)]
    pub fn set_current_period(&mut self, p: Option<u32>) {
        self.current_period = p;
    }

    #[inline(always)]
    pub fn get_current_period(&self) -> Option<u32> {
        self.current_period
    }

    #[inline(always)]
    pub fn update_release_time(&mut self, time: awkernel_lib::time::Time) {
        // This could potentially cause deadline misses in the future.
        self.release_time = Some(time);
    }

    #[inline(always)]
    pub fn get_release_time(&self) -> Option<awkernel_lib::time::Time> {
        self.release_time
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

#[derive(Debug, Clone)]
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
        scheduler_type: SchedulerType,
        dag_info: Option<DagInfo>,
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
                    state: State::Initialized,
                    num_preempt: 0,
                    last_executed_time: awkernel_lib::time::Time::now(),
                    absolute_deadline: None,
                    need_sched: false,
                    need_preemption: false,
                    panicked: false,
                    dag_info,
                    current_period: None,
                    need_terminate: false,

                    #[cfg(not(feature = "no_preempt"))]
                    thread: None,

                    release_time: None,
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
    use alloc::string::{String, ToString};
    use awkernel_lib::{cpu::NUM_MAX_CPU, device_tree::node};
    use core::{ptr::{read_volatile, write_volatile}};
    use crate::task::{self, get_task_period};
    use core::sync::atomic::{AtomicU32, Ordering};
    use array_macro::array;
    

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
    #[derive(Debug, Clone)]
    pub struct NodeRecord{
        pub period_count: u32,
        pub dag_info: task::DagInfo,
        // start: u64,
        // end: u64,
        // preempt_count: u32,
        // core_id: u8,
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

    use awkernel_lib::sync::{mcs::MCSNode, mutex::Mutex};
    const MAX_LOGS: usize = 8192;

    static SEND_OUTER_TIMESTAMP: Mutex<Option<[[u64; MAX_DAGS]; MAX_LOGS]>> = Mutex::new(None);
    static RECV_OUTER_TIMESTAMP: Mutex<Option<[[u64; MAX_DAGS]; MAX_LOGS]>> = Mutex::new(None);
    static ABSOLUTE_DEADLINE: Mutex<Option<[[u64; MAX_DAGS]; MAX_LOGS]>> = Mutex::new(None);
    static RELATIVE_DEADLINE: Mutex<Option<[[u64; MAX_DAGS]; MAX_LOGS]>> = Mutex::new(None);
    static DAG_PREEMPT_COUNT: Mutex<Option<[[u32; MAX_DAGS]; MAX_LOGS]>> = Mutex::new(None);

    //DAG+1
    const MAX_DAGS: usize = 4;
    pub static PERIOD_COUNT: [AtomicU32; MAX_DAGS] = array![_ => AtomicU32::new(0); MAX_DAGS];
    pub static SINK_COUNT: [AtomicU32; MAX_DAGS] = array![_ => AtomicU32::new(0); MAX_DAGS];

    const MAX_NODES: usize = 20;
    static NODE_START: Mutex<Option<[[u64; MAX_NODES]; MAX_LOGS]>> = Mutex::new(None);
    static NODE_FINISH: Mutex<Option<[[u64; MAX_NODES]; MAX_LOGS]>> = Mutex::new(None);
    static NODE_PREEMPT_COUNT: Mutex<Option<[[u32; MAX_NODES]; MAX_LOGS]>> = Mutex::new(None);
    static NODE_CORE: Mutex<Option<[[u8; MAX_NODES]; MAX_LOGS]>> = Mutex::new(None);

    //pubsub
    const MAX_PUBSUB: usize = 3;
    static PUBLISH: Mutex<Option<[[[u64; MAX_NODES]; MAX_PUBSUB]; MAX_LOGS]>> = Mutex::new(None);
    static SUBSCRIBE: Mutex<Option<[[[u64; MAX_NODES]; MAX_PUBSUB]; MAX_LOGS]>> = Mutex::new(None);
    pub static PUB_COUNT: [AtomicU32; MAX_PUBSUB] = array![_ => AtomicU32::new(0); MAX_PUBSUB];
    pub static SUB_COUNT: [AtomicU32; MAX_PUBSUB] = array![_ => AtomicU32::new(0); MAX_PUBSUB];

    pub fn reset_perf_logs() {
        for i in 0..MAX_PUBSUB {
            PUB_COUNT[i].store(0, Ordering::Relaxed);
            SUB_COUNT[i].store(0, Ordering::Relaxed);
        }
        for i in 0..MAX_DAGS {
            PERIOD_COUNT[i].store(0, Ordering::Relaxed);
            SINK_COUNT[i].store(0, Ordering::Relaxed);
        }
        *SEND_OUTER_TIMESTAMP.lock(&mut MCSNode::new()) = None;
        *RECV_OUTER_TIMESTAMP.lock(&mut MCSNode::new()) = None;
        *ABSOLUTE_DEADLINE.lock(&mut MCSNode::new()) = None;
        *RELATIVE_DEADLINE.lock(&mut MCSNode::new()) = None;
        *NODE_START.lock(&mut MCSNode::new()) = None;
        *NODE_FINISH.lock(&mut MCSNode::new()) = None;
    }

    pub fn increment_pub_count(pub_id: usize) {
        assert!(pub_id < MAX_PUBSUB, "Pub ID out of bounds");
        PUB_COUNT[pub_id].fetch_add(1, Ordering::Relaxed);
    }

    pub fn increment_sub_count(sub_id: usize) {
        assert!(sub_id < MAX_PUBSUB, "Sub ID out of bounds");
        SUB_COUNT[sub_id].fetch_add(1, Ordering::Relaxed);
    }

    pub fn get_pub_count(pub_id: usize) -> u32 {
        assert!(pub_id < MAX_PUBSUB, "Pub ID out of bounds");
        PUB_COUNT[pub_id].load(Ordering::Relaxed)
    }

    pub fn get_sub_count(sub_id: usize) -> u32 {
        assert!(sub_id < MAX_PUBSUB, "Sub ID out of bounds");
        SUB_COUNT[sub_id].load(Ordering::Relaxed)
    }

    pub fn increment_period_count(dag_id: usize) {
        assert!(dag_id < MAX_DAGS, "DAG ID out of bounds");
        PERIOD_COUNT[dag_id].fetch_add(1, Ordering::Relaxed);
    }

    pub fn get_period_count(dag_id: usize) -> u32 {
        assert!(dag_id < MAX_DAGS, "DAG ID out of bounds");
        PERIOD_COUNT[dag_id].load(Ordering::Relaxed)
    }

    pub fn increment_sink_count(dag_id: usize) {
        assert!(dag_id < MAX_DAGS, "DAG ID out of bounds");
        SINK_COUNT[dag_id].fetch_add(1, Ordering::Relaxed);
    }

    pub fn get_sink_count(dag_id: usize) -> u32 {
        assert!(dag_id < MAX_DAGS, "DAG ID out of bounds");
        SINK_COUNT[dag_id].load(Ordering::Relaxed)
    }

    pub fn update_pre_send_outer_timestamp_at(index: usize, new_timestamp: u64, dag_id: u32) {
        assert!(index < MAX_LOGS, "Timestamp index out of bounds");

        let mut node = MCSNode::new();
        let mut recorder_opt = SEND_OUTER_TIMESTAMP.lock(&mut node);

        let recorder = recorder_opt.get_or_insert_with(|| [[0; MAX_DAGS]; MAX_LOGS]);

        if recorder[index][dag_id as usize] == 0 {
            recorder[index][dag_id as usize] = new_timestamp;
        }
    }

    pub fn update_fin_recv_outer_timestamp_at(index: usize, new_timestamp: u64, dag_id: u32) {
        assert!(index < MAX_LOGS, "Timestamp index out of bounds");

        let mut node = MCSNode::new();
        let mut recorder_opt = RECV_OUTER_TIMESTAMP.lock(&mut node);

        let recorder = recorder_opt.get_or_insert_with(|| [[0; MAX_DAGS]; MAX_LOGS]);

        if (dag_id as usize) < recorder[0].len() {
            recorder[index][dag_id as usize] = new_timestamp;
        }
    }

    pub fn update_absolute_deadline_timestamp_at(index: usize, deadline: u64, dag_id: u32){
        assert!(index < MAX_LOGS, "Timestamp index out of bounds");

        let mut node = MCSNode::new();
        let mut recorder_opt = ABSOLUTE_DEADLINE.lock(&mut node);

        let recorder = recorder_opt.get_or_insert_with(|| [[0; MAX_DAGS]; MAX_LOGS]);

        if recorder[index][dag_id as usize] == 0 {
            recorder[index][dag_id as usize] = deadline;
        }
        
    }

    pub fn update_relative_deadline_timestamp_at(index: usize, deadline: u64, dag_id: u32){
        assert!(index < MAX_LOGS, "Timestamp index out of bounds");

        let mut node = MCSNode::new();
        let mut recorder_opt = RELATIVE_DEADLINE.lock(&mut node);

        let recorder = recorder_opt.get_or_insert_with(|| [[0; MAX_DAGS]; MAX_LOGS]);

        if recorder[index][dag_id as usize] == 0 {
            recorder[index][dag_id as usize] = deadline;
        }
        
    }

    pub fn node_start(node:NodeRecord, start: u64){
        // assert!(index < MAX_LOGS, "Node log index out of bounds");
        assert!((node.dag_info.node_id as usize) < MAX_NODES, "Node ID out of bounds");

        let mut mcs_node = MCSNode::new();
        let mut recorder_opt = NODE_START.lock(&mut mcs_node);

        let recorder = recorder_opt.get_or_insert_with(|| [[0; MAX_NODES]; MAX_LOGS]);

        if recorder[node.period_count as usize][node.dag_info.node_id as usize] == 0 {
            recorder[node.period_count as usize][node.dag_info.node_id as usize] = start;
        }
    }

    pub fn node_finish(node:NodeRecord, finish: u64){
        // assert!(index < MAX_LOGS, "Node log index out of bounds");
        assert!((node.dag_info.node_id as usize) < MAX_NODES, "Node ID out of bounds");

        let mut mcs_node = MCSNode::new();
        let mut recorder_opt = NODE_FINISH.lock(&mut mcs_node);

        let recorder = recorder_opt.get_or_insert_with(|| [[0; MAX_NODES]; MAX_LOGS]);

        if recorder[node.period_count as usize][node.dag_info.node_id as usize] == 0 {
            recorder[node.period_count as usize][node.dag_info.node_id as usize] = finish;
        }
    }

    pub fn node_preempt(node:NodeRecord){
        // assert!(index < MAX_LOGS, "Node log index out of bounds");
        assert!((node.dag_info.node_id as usize) < MAX_NODES, "Node ID out of bounds");

        let mut mcs_node = MCSNode::new();
        let mut recorder_opt = NODE_PREEMPT_COUNT.lock(&mut mcs_node);

        let recorder = recorder_opt.get_or_insert_with(|| [[0; MAX_NODES]; MAX_LOGS]);

        recorder[node.period_count as usize][node.dag_info.node_id as usize] += 1;
    }

    pub fn dag_preempt(node:NodeRecord){
        // assert!(index < MAX_LOGS, "Node log index out of bounds");
        assert!((node.dag_info.dag_id as usize) < MAX_DAGS, "DAG ID out of bounds");

        let mut mcs_node = MCSNode::new();
        let mut recorder_opt = DAG_PREEMPT_COUNT.lock(&mut mcs_node);

        let recorder = recorder_opt.get_or_insert_with(|| [[0; MAX_DAGS]; MAX_LOGS]);

        recorder[node.period_count as usize][node.dag_info.dag_id as usize] += 1;
    }

    pub fn publish_timestamp_at(index: usize, new_timestamp: u64, pub_id: u32, node_id: u32) {
        assert!(index < MAX_LOGS, "Timestamp index out of bounds");
        assert!((pub_id as usize) < MAX_PUBSUB, "Publish ID out of bounds");

        let mut node = MCSNode::new();
        let mut recorder_opt = PUBLISH.lock(&mut node);

        let recorder = recorder_opt.get_or_insert_with(|| [[[0; MAX_NODES]; MAX_PUBSUB]; MAX_LOGS]);

        if recorder[index][pub_id as usize][node_id as usize] == 0 {
            recorder[index][pub_id as usize][node_id as usize] = new_timestamp;
        }
    }

    pub fn subscribe_timestamp_at(index: usize, new_timestamp: u64, sub_id: u32, node_id: u32) {
        assert!(index < MAX_LOGS, "Timestamp index out of bounds");
        assert!((sub_id as usize) < MAX_PUBSUB, "Subscribe ID out of bounds");

        let mut node = MCSNode::new();
        let mut recorder_opt = SUBSCRIBE.lock(&mut node);

        let recorder = recorder_opt.get_or_insert_with(|| [[[0; MAX_NODES]; MAX_PUBSUB]; MAX_LOGS]);

        if recorder[index][sub_id as usize][node_id as usize] == 0 {
            recorder[index][sub_id as usize][node_id as usize] = new_timestamp;
        }
    }

    // For precision of the cycle
    pub fn print_timestamp_table() {
        let mut node1 = MCSNode::new();
        let mut node2 = MCSNode::new();
        let mut node3 = MCSNode::new();
        let mut node4 = MCSNode::new();
        let mut node5 = MCSNode::new();

        let send_outer_opt = SEND_OUTER_TIMESTAMP.lock(&mut node1);
        let recv_outer_opt = RECV_OUTER_TIMESTAMP.lock(&mut node2);
        let absolute_deadline_opt = ABSOLUTE_DEADLINE.lock(&mut node3);
        let relative_deadline_opt = RELATIVE_DEADLINE.lock(&mut node4);
        let dag_preempt_opt = DAG_PREEMPT_COUNT.lock(&mut node5);

        log::info!("--- Timestamp Summary (in nanoseconds) ---");
        log::info!(
            "{: ^5} | {: ^5} | {: ^14} | {: ^14} | {: ^14} | {: ^14} | {: ^14} | {: ^14}",
            "Index",
            "DAG-ID",
            "Send-Outer",
            "Recv-Outer",
            "Latency",
            "Absolute Deadline",
            "Relative Deadline",
            "DAG Preemptions"
        );

        log::info!("-----|--------|----------------|----------------|----------------|--------------------|--------------------|--------------------|--------------------");

        for i in 0..MAX_LOGS {
            for j in 1..MAX_DAGS {
                let pre_send_outer = send_outer_opt.as_ref().map_or(0, |arr| arr[i][j]);
                let fin_recv_outer = recv_outer_opt.as_ref().map_or(0, |arr| arr[i][j]);
                let absolute_deadline = absolute_deadline_opt.as_ref().map_or(0, |arr| arr[i][j]);
                let relative_deadline = relative_deadline_opt.as_ref().map_or(0, |arr| arr[i][j]);
                let dag_preempt = dag_preempt_opt.as_ref().map_or(0, |arr| arr[i][j]);

                if pre_send_outer != 0 || fin_recv_outer != 0 || absolute_deadline != 0 || relative_deadline != 0 || dag_preempt != 0 {
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
                        "{: >5} | {: >5} | {: >14} | {: >14} | {: >14} | {: >20} | {: >20} | {: >20}",
                        i,
                        format_ts(j as u64),
                        format_ts(pre_send_outer),
                        format_ts(fin_recv_outer),
                        latency_str,
                        format_ts(absolute_deadline),
                        format_ts(relative_deadline),
                        format_ts(dag_preempt as u64),
                    );
                }
            }
        }
        log::info!("----------------------------------------------------------");
    }

    /// Print per-node timing table.
    /// Columns: DAG ID | node id | period | start(ns) | end(ns) | duration(ns) | preemptions | core
    /// not used now
    pub fn print_node_table() {
        let mut node1 = MCSNode::new();
        let mut node2 = MCSNode::new();
        let mut node3 = MCSNode::new();
        let mut node4 = MCSNode::new();

        let node_start_opt = NODE_START.lock(&mut node1);
        let node_finish_opt = NODE_FINISH.lock(&mut node2);
        let node_preempt_opt = NODE_PREEMPT_COUNT.lock(&mut node3);
        let node_core_opt = NODE_CORE.lock(&mut node4);

        log::info!("--- Per-node Timing Summary (in nanoseconds) ---");
        log::info!(
            "{:<5} | {:<6} | {:<7} | {:<20} | {:<20} | {:<20} | {:<12} | {:<4}",
            "Index",
            "DAG-ID",
            "NODE-ID",
            "start(ns)",
            "end(ns)",
            "duration(ns)",
            "preemptions",
            "core"
        );
        log::info!("------|--------|---------|----------------------|----------------------|----------------------|-----");

        for i in 0..MAX_LOGS {
            for j in 0..MAX_NODES {
                let start = node_start_opt.as_ref().map_or(0, |arr| arr[i][j]);
                let finish = node_finish_opt.as_ref().map_or(0, |arr| arr[i][j]);
                let preempt_count = node_preempt_opt.as_ref().map_or(0, |arr| arr[i][j]);
                let core_id = node_core_opt.as_ref().map_or(0, |arr| arr[i][j]);
                // let period_count = node_period_count_opt.as_ref().map_or(0, |arr| arr[i][j]);

                if start != 0 || finish != 0 || preempt_count != 0 {

                    let format_ts = |ts: u64| -> String {
                            ts.to_string()
                    };

                    let duration = if start != 0 && finish != 0 {
                        finish.saturating_sub(start).to_string()
                    } else {
                        "-".to_string()
                    };

                    log::info!(
                        "{:<5} | {:<6} | {:<7} | {:<20} | {:<20} | {:<20} | {:<12} | {:<4}",
                        i,
                        1, // DAG ID (assumed 1 for simplicity)
                        format_ts(j as u64),
                        format_ts(start),
                        format_ts(finish),
                        duration,
                        format_ts(preempt_count as u64),
                        format_ts(core_id as u64),
                    );
                }
            }
        }
        log::info!("--------------------------------------------------------------");
    }

    // For pubsub communication latency
    pub fn print_pubsub_table() {
        let mut node1 = MCSNode::new();
        let mut node2 = MCSNode::new();

        let publish_opt = PUBLISH.lock(&mut node1);
        let subscribe_opt = SUBSCRIBE.lock(&mut node2);

        log::info!("--- Pub/Sub Timestamp Summary (in nanoseconds) ---");
        log::info!(
            "{: ^5} | {: ^10} | {: ^7} | {: ^14} | {: ^14}",
            "Index",
            "Pub/Sub ID",
            "Node ID",
            "Publish Time",
            "Subscribe Time"
        );
        log::info!("-----|------------|---------|----------------|----------------");
        for i in 0..MAX_LOGS {
            for j in 0..MAX_PUBSUB {
                for k in 0..MAX_NODES {
                    let publish_time = publish_opt.as_ref().map_or(0, |arr| arr[i][j][k]);
                    let subscribe_time = subscribe_opt.as_ref().map_or(0, |arr| arr[i][j][k]);

                    if publish_time != 0 || subscribe_time != 0 {
                        let format_ts = |ts: u64| -> String {
                            if ts == 0 {
                                "-".to_string()
                            } else {
                                ts.to_string()
                            }
                        };

                        log::info!(
                            "{: >5} | {: >10} | {: >7} | {: >14} | {: >14}",
                            i,
                            j,
                            k,
                            format_ts(publish_time),
                            format_ts(subscribe_time),
                        );
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

    fn update_time_and_state_for_dag(next_state: PerfState) {
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
                    // log::info!("PreemptionTime CPU:{} Diff:{}", cpu_id, diff);
                    let t = read_volatile(&INTERRUPT_TIME[cpu_id]);
                    write_volatile(&mut INTERRUPT_TIME[cpu_id], t + diff);
                    let c = read_volatile(&INTERRUPT_COUNT[cpu_id]);
                    write_volatile(&mut INTERRUPT_COUNT[cpu_id], c + 1);
                    let wcet = read_volatile(&INTERRUPT_WCET[cpu_id]);
                    write_volatile(&mut INTERRUPT_WCET[cpu_id], wcet.max(diff));
                },
                PerfState::ContextSwitch => unsafe {
                    // log::info!("ContextSwitchTime CPU:{} Diff:{}", cpu_id, diff);
                    let t = read_volatile(&CONTEXT_SWITCH_TIME[cpu_id]);
                    write_volatile(&mut CONTEXT_SWITCH_TIME[cpu_id], t + diff);
                    let c = read_volatile(&CONTEXT_SWITCH_COUNT[cpu_id]);
                    write_volatile(&mut CONTEXT_SWITCH_COUNT[cpu_id], c + 1);
                    let wcet = read_volatile(&CONTEXT_SWITCH_WCET[cpu_id]);
                    write_volatile(&mut CONTEXT_SWITCH_WCET[cpu_id], wcet.max(diff));
                },
                PerfState::ContextSwitchMain => unsafe {
                    // log::info!("ContextSwitchMainTime CPU:{} Diff:{}", cpu_id, diff);
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

        // Check the current task
        if let Some(task_id) = task::get_current_task(cpu_id) {
            if let Some(task) = task::get_task(task_id) {
                let dag_info = task.info.lock(&mut task::MCSNode::new()).get_dag_info();
                if dag_info.is_some() {
                    // DAG task-specific handling
                    update_time_and_state_for_dag(PerfState::Interrupt);
                    // Create a NodeRecord with the current period count and call node_preempt
                    // let period = get_task_period(task_id).unwrap();
                    // if let Some(di) = dag_info {
                    //     let nr = NodeRecord {
                    //         period_count: period,
                    //         dag_info: task::DagInfo { dag_id: di.dag_id, node_id: di.node_id },
                    //     };
                    //     dag_preempt(nr);
                    // }
                } else {
                    // Normal task-specific handling
                    update_time_and_state(PerfState::Interrupt);
                }
            }
        } else {
            // Default handling if no task is running
            update_time_and_state(PerfState::Interrupt);
        }

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
        let cpu_id = awkernel_lib::cpu::cpu_id();

        if let Some(task_id) = task::get_current_task(cpu_id) {
            if let Some(task) = task::get_task(task_id) {
                let dag_info = task.info.lock(&mut task::MCSNode::new()).get_dag_info();
                if dag_info.is_some() {
                    // DAG task-specific handling
                    update_time_and_state_for_dag(PerfState::ContextSwitch);
                } else {
                    // Normal task-specific handling
                    update_time_and_state(PerfState::ContextSwitch);
                }
            }
        } else {
            // Default handling if no task is running
            update_time_and_state(PerfState::ContextSwitch);
        }
    }

    #[inline(always)]
    pub(crate) fn start_context_switch_main() {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        if let Some(task_id) = task::get_current_task(cpu_id) {
            if let Some(task) = task::get_task(task_id) {
                let dag_info = task.info.lock(&mut task::MCSNode::new()).get_dag_info();
                if dag_info.is_some() {
                    // DAG task-specific handling
                    update_time_and_state_for_dag(PerfState::ContextSwitchMain);
                } else {
                    // Normal task-specific handling
                    update_time_and_state(PerfState::ContextSwitchMain);
                }
            }
        } else {
            // Default handling if no task is running
            update_time_and_state(PerfState::ContextSwitchMain);
        }
    }

    pub fn count_preempt() {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        if let Some(task_id) = task::get_current_task(cpu_id) {
            if let Some(task) = task::get_task(task_id) {
                let dag_info = task.info.lock(&mut task::MCSNode::new()).get_dag_info();
                if dag_info.is_some() {
                    // DAG task-specific handling
                    let period = get_task_period(task_id).unwrap();
                    if let Some(di) = dag_info {
                        let nr = NodeRecord {
                            period_count: period,
                            dag_info: task::DagInfo { dag_id: di.dag_id, node_id: di.node_id },
                        };
                        dag_preempt(nr);
                    }
                }
            }
        }
    }

    // pub fn memo_core(){
    //     let cpu_id = awkernel_lib::cpu::cpu_id();

    //     if let Some(task_id) = task::get_current_task(cpu_id) {
    //         if let Some(task) = task::get_task(task_id) {
    //             let dag_info = task.info.lock(&mut task::MCSNode::new()).get_dag_info();
    //             if dag_info.is_some() {
    //                 // DAG task-specific handling
    //                 let period = get_task_period(task_id).unwrap();
    //                 if let Some(di) = dag_info {
    //                     let nr = NodeRecord {
    //                         period_count: period,
    //                         dag_info: task::DagInfo { dag_id: di.dag_id, node_id: di.node_id },
    //                     };
    //                     node_core(nr, cpu_id as u8);
    //                 }
    //             }
    //         }
    //     }
    // }

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

    /// Compare release_time and timenow with absolute_deadline.
    pub fn compare_release_and_timenow_with_deadline(release_time: awkernel_lib::time::Time, timenow: u64, absolute_deadline: u64) {
        let release_time_millis = release_time.as_millis() as u64;
        let timenow_millis = timenow/1000000 as u64;
        let absolute_deadline_ms = absolute_deadline/1000;
        // let absolute_difference = (release_time_millis - timenow_millis).abs();
        log::info!("Release time: {} ms, Current time: {} ms, Absolute deadline: {} ms", release_time_millis, timenow_millis, absolute_deadline_ms);

        if timenow_millis > absolute_deadline_ms  {
            log::warn!("Deadline missed! Difference: {} ms", timenow_millis-absolute_deadline_ms);
        } else {
            log::info!("Within deadline. Difference: {} ms", absolute_deadline_ms-timenow_millis);
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
                // [start] context_switch_main
                #[cfg(feature = "perf")]
                perf::start_context_switch_main();
                // If the next task is a preempted task, then the current task will yield to the thread holding the next task.
                // After that, the current thread will be stored in the thread pool.
                let mut node = MCSNode::new();
                let mut info = task.info.lock(&mut node);

                if let Some(ctx) = info.take_preempt_context() {
                    info.update_last_executed();
                    drop(info);

                    //別のstart関数を置いて改変
                    unsafe { preempt::yield_and_pool(ctx) };

                    #[cfg(feature = "perf")]
                    perf::start_kernel();

                    continue;
                }
                #[cfg(feature = "perf")]
                    perf::start_kernel();
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

                    {
                        let mut node = MCSNode::new();
                        let mut info = task.info.lock(&mut node);

                        if info.need_terminate {
                            info.state = State::Terminated;
                            info.need_terminate = false;

                            #[cfg(feature = "perf")]
                            perf::start_kernel();

                            #[cfg(all(
                                any(target_arch = "aarch64", target_arch = "x86_64"),
                                not(feature = "std")
                            ))]
                            {
                                awkernel_lib::interrupt::disable();
                            }

                            return Poll::Ready(Ok(()));
                        }
                    }

                    #[cfg(feature = "perf")]
                    perf::start_task();
                    //preemption関連が若干面倒：cpuに割り付けられるまで(終了)

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

/// Set the current period observed for a task (stores into TaskInfo.current_period).
pub fn set_task_period(task_id: u32, period: Option<u32>) {
    if let Some(task) = get_task(task_id) {
        let mut node = MCSNode::new();
        let mut info = task.info.lock(&mut node);
        info.set_current_period(period);
    }
}

/// Get the current period recorded for a task, if any.
pub fn get_task_period(task_id: u32) -> Option<u32> {
    if let Some(task) = get_task(task_id) {
        let mut node = MCSNode::new();
        let info = task.info.lock(&mut node);
        info.get_current_period()
    } else {
        None
    }
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

#[inline(always)]
pub fn set_need_terminate(task_id: u32) {
    let task = {
        let mut node = MCSNode::new();
        let tasks = TASKS.lock(&mut node);

        if let Some(task) = tasks.id_to_task.get(&task_id) {
            let mut node = MCSNode::new();
            let mut info = task.info.lock(&mut node);
            info.need_terminate = true;
            Some(task.clone())
        } else {
            None
        }
    };

    if let Some(task) = task {
        task.wake();
    }
}


#[inline(always)]
pub fn terminate_task(task_id: u32) {
    let task = {
        let mut node = MCSNode::new();
        let tasks = TASKS.lock(&mut node);
        tasks.id_to_task.get(&task_id).cloned()
    };

    if let Some(task) = task {
        let mut node = MCSNode::new();
        let mut info = task.info.lock(&mut node);
        info.state = State::Terminated;
    }

    let mut node = MCSNode::new();
    let mut tasks = TASKS.lock(&mut node);
    tasks.remove(task_id);
}

#[inline(always)]
pub fn whether_dag(task: &Arc<Task>) -> bool {
    let mut node = MCSNode::new();
    let info = task.info.lock(&mut node);
    info.get_dag_info().is_some()
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
    let mut num_tasks = NUM_TASK_IN_QUEUE.load(Ordering::Relaxed);
    let num_cpu = awkernel_lib::cpu::num_cpu();

    for i in 1..num_cpu {
        if num_tasks == 0 {
            break;
        }

        if awkernel_lib::cpu::wake_cpu(i) {
            num_tasks -= 1;
        }
    }
}
