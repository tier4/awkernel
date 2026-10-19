//! A generic EDF scheduler for tasks that may belong to a DAG.
//!
//! [`DagEdfScheduler`] holds everything the DAG-aware EDF schedulers share: the run queue ordered
//! by absolute deadline, the wake and dispatch logic, and the preemption. A concrete scheduler,
//! such as GEDF or REDF, is a [`DagEdfPolicy`] that says only how the deadline is computed.
//!
//! To add a scheduler of this family:
//! 1. Add a variant to `SchedulerType`, and register it in `PRIORITY_LIST`, `equals()` and
//!    `get_scheduler()` in `scheduler.rs`.
//! 2. Implement [`DagEdfPolicy`] on a marker type, and define
//!    `pub static SCHEDULER: DagEdfScheduler<MyPolicy> = DagEdfScheduler::new();`.

use core::{cmp::max, marker::PhantomData};

use super::{Scheduler, SchedulerType, Task};
use crate::{
    dag::{get_dag, to_node_index, Dag, NodeIndex},
    scheduler::GLOBAL_WAKE_GET_MUTEX,
    scheduler::{
        get_priority, peek_preemption_pending, push_preemption_pending, PREEMPTION_ENABLED,
    },
    task::{
        get_task, get_tasks_running, set_current_task, set_need_preemption, DagInfo, State,
        MAX_TASK_PRIORITY,
    },
};
use alloc::{collections::BinaryHeap, sync::Arc, vec::Vec};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

/// The scheduler-specific part of a [`DagEdfScheduler`].
pub trait DagEdfPolicy: 'static {
    /// The scheduler type with a dummy payload. It selects the priority of the scheduler.
    const SCHEDULER_TYPE: SchedulerType;

    /// The name of the scheduler for panic messages.
    const NAME: &'static str;

    /// Returns the relative deadline in `scheduler_type`, which is the deadline of a task that
    /// does not belong to a DAG, or `None` if `scheduler_type` is not of this scheduler.
    fn relative_deadline(scheduler_type: &SchedulerType) -> Option<u64>;

    /// Returns the absolute deadline of the job that the node `node_idx` of `dag` processes
    /// next. `release` is true if this wake may release that job. The policy gets the release
    /// time of the job with `Dag::get_or_release_release_time` or
    /// `Dag::get_or_release_absolute_deadline`, and passes `wake_time` as the release time.
    fn dag_deadline(dag: &Dag, node_idx: NodeIndex, release: bool, wake_time: u64) -> u64;
}

/// Returns the absolute deadline of the DAG job that the node of `dag_info` processes next,
/// according to the policy `P`.
///
/// A wake of the source node in any `state` except `State::Preempted` may release that job.
///
/// # Panics
///
/// Panics if the DAG does not exist, or if the policy panics.
pub fn calculate_dag_deadline<P: DagEdfPolicy>(
    dag_info: &DagInfo,
    wake_time: u64,
    state: State,
) -> u64 {
    let dag_id = dag_info.dag_id;
    let dag =
        get_dag(dag_id).unwrap_or_else(|| panic!("{} scheduler: DAG {dag_id} not found", P::NAME));

    // The wake of a preempted task resumes it and does not release a job. Any other wake
    // of the source node at an unreleased job must come from its `Interval` tick. After the
    // source node finishes a job, it waits only for that tick, because it has no subscriber.
    let release = state != State::Preempted;

    P::dag_deadline(&dag, to_node_index(dag_info.node_id), release, wake_time)
}

pub struct DagEdfScheduler<P: DagEdfPolicy> {
    data: Mutex<Option<DagEdfData>>, // Run queue.
    priority: u8,
    policy: PhantomData<fn() -> P>,
}

struct DagEdfTask {
    task: Arc<Task>,
    absolute_deadline: u64,
    wake_time: u64,
}

impl PartialOrd for DagEdfTask {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for DagEdfTask {
    fn eq(&self, other: &Self) -> bool {
        self.absolute_deadline == other.absolute_deadline && self.wake_time == other.wake_time
    }
}

impl Ord for DagEdfTask {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        match other.absolute_deadline.cmp(&self.absolute_deadline) {
            core::cmp::Ordering::Equal => other.wake_time.cmp(&self.wake_time),
            other => other,
        }
    }
}

impl Eq for DagEdfTask {}

struct DagEdfData {
    queue: BinaryHeap<DagEdfTask>,
}

impl DagEdfData {
    fn new() -> Self {
        Self {
            queue: BinaryHeap::new(),
        }
    }
}

impl<P: DagEdfPolicy> DagEdfScheduler<P> {
    pub const fn new() -> Self {
        Self {
            data: Mutex::new(None),
            priority: get_priority(&P::SCHEDULER_TYPE),
            policy: PhantomData,
        }
    }

    fn invoke_preemption(&self, task: Arc<Task>) -> bool {
        if !PREEMPTION_ENABLED {
            return false;
        }

        let tasks_running = get_tasks_running()
            .into_iter()
            .filter(|rt| rt.task_id != 0) // Filter out idle CPUs
            .collect::<Vec<_>>();

        // If the task has already been running, preempt is not required.
        if tasks_running.is_empty() || tasks_running.iter().any(|rt| rt.task_id == task.id) {
            return false;
        }

        let preemption_target = tasks_running
            .iter()
            .filter_map(|rt| {
                get_task(rt.task_id).map(|t| {
                    let highest_pending = peek_preemption_pending(rt.cpu_id).unwrap_or(t.clone());
                    (max(t, highest_pending), rt.cpu_id)
                })
            })
            .min()
            .unwrap();

        let (target_task, target_cpu) = preemption_target;
        if task.preempts(&target_task) {
            push_preemption_pending(target_cpu, task);
            let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
            set_need_preemption(target_task.id, target_cpu);
            awkernel_lib::interrupt::send_ipi(preempt_irq, target_cpu as u32);

            // NOTE(atsushi421): Currently, preemption is requested regardless of the number of idle CPUs.
            // While this implementation easily prevents priority inversion, it may also cause unnecessary preemption.
            // Therefore, a more sophisticated implementation will be considered in the future.

            return true;
        }

        false
    }
}

impl<P: DagEdfPolicy> Default for DagEdfScheduler<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: DagEdfPolicy> Scheduler for DagEdfScheduler<P> {
    fn wake_task(&self, task: Arc<Task>) {
        let (wake_time, absolute_deadline) = {
            let mut node_inner = MCSNode::new();
            let mut info = task.info.lock(&mut node_inner);
            let dag_info = info.get_dag_info();
            let Some(relative_deadline) = P::relative_deadline(&info.scheduler_type) else {
                unreachable!()
            };

            let wake_time = awkernel_lib::delay::uptime();
            let absolute_deadline = if let Some(ref dag_info) = dag_info {
                calculate_dag_deadline::<P>(dag_info, wake_time, info.state)
            } else {
                // If dag_info is not present, the task is treated as a regular task, and
                // the absolute_deadline is calculated using the scheduler's relative_deadline.
                wake_time + relative_deadline
            };

            task.priority
                .update_priority_info(self.priority, MAX_TASK_PRIORITY - absolute_deadline);
            info.update_absolute_deadline(absolute_deadline);

            (wake_time, absolute_deadline)
        };

        let mut node = MCSNode::new();
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);
        if !self.invoke_preemption(task.clone()) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data.lock(&mut node_inner);
            let internal_data = data.get_or_insert_with(DagEdfData::new);
            internal_data.queue.push(DagEdfTask {
                task: task.clone(),
                absolute_deadline,
                wake_time,
            });
        }
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        #[allow(clippy::question_mark)]
        let data = match data.as_mut() {
            Some(data) => data,
            None => return None,
        };

        loop {
            // Pop a task from the run queue.
            let task = data.queue.pop()?;

            // Make the state of the task Running.
            {
                let mut node = MCSNode::new();
                let mut task_info = task.task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }

                if task_info.state == State::Preempted {
                    task_info.need_preemption = false;
                }
                if execution_ensured {
                    task_info.state = State::Running;
                    set_current_task(awkernel_lib::cpu::cpu_id(), task.task.id);
                }
            }

            return Some(task.task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        P::SCHEDULER_TYPE
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}
