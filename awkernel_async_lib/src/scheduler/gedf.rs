//! A GEDF scheduler.

use core::cmp::max;

use super::{Scheduler, SchedulerType, Task};
use crate::{
    dag::{get_dag, to_node_index},
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

pub struct GEDFScheduler {
    data: Mutex<Option<GEDFData>>, // Run queue.
    priority: u8,
}

struct GEDFTask {
    task: Arc<Task>,
    absolute_deadline: u64,
    wake_time: u64,
}

impl PartialOrd for GEDFTask {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for GEDFTask {
    fn eq(&self, other: &Self) -> bool {
        self.absolute_deadline == other.absolute_deadline && self.wake_time == other.wake_time
    }
}

impl Ord for GEDFTask {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        match other.absolute_deadline.cmp(&self.absolute_deadline) {
            core::cmp::Ordering::Equal => other.wake_time.cmp(&self.wake_time),
            other => other,
        }
    }
}

impl Eq for GEDFTask {}

struct GEDFData {
    queue: BinaryHeap<GEDFTask>,
}

impl GEDFData {
    fn new() -> Self {
        Self {
            queue: BinaryHeap::new(),
        }
    }
}

impl Scheduler for GEDFScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let (wake_time, absolute_deadline) = {
            let mut node_inner = MCSNode::new();
            let mut info = task.info.lock(&mut node_inner);
            let dag_info = info.get_dag_info();
            match info.scheduler_type {
                SchedulerType::GEDF(relative_deadline) => {
                    let wake_time = awkernel_lib::delay::uptime();
                    let absolute_deadline = if let Some(ref dag_info) = dag_info {
                        calculate_and_update_dag_deadline(dag_info, wake_time, info.state)
                    } else {
                        // If dag_info is not present, the task is treated as a regular task, and
                        // the absolute_deadline is calculated using the scheduler's relative_deadline.
                        wake_time + relative_deadline
                    };

                    task.priority
                        .update_priority_info(self.priority, MAX_TASK_PRIORITY - absolute_deadline);
                    info.update_absolute_deadline(absolute_deadline);

                    (wake_time, absolute_deadline)
                }
                _ => unreachable!(),
            }
        };

        let mut node = MCSNode::new();
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);
        if !self.invoke_preemption(task.clone()) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data.lock(&mut node_inner);
            let internal_data = data.get_or_insert_with(GEDFData::new);
            internal_data.queue.push(GEDFTask {
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
        SchedulerType::GEDF(0)
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

pub static SCHEDULER: GEDFScheduler = GEDFScheduler {
    data: Mutex::new(None),
    priority: get_priority(&SchedulerType::GEDF(0)),
};

impl GEDFScheduler {
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

/// Returns the absolute deadline of the DAG job that the node of `dag_info` processes next.
/// A wake of the source node in any `state` except `State::Preempted` releases that job
/// with `wake_time` plus the sink relative deadline, if it is not released yet. Any other wake
/// before the release gets that value without a release.
///
/// # Panics
///
/// Panics if the DAG does not exist, has no node `dag_info.node_id`, or has no sink relative
/// deadline.
pub fn calculate_and_update_dag_deadline(dag_info: &DagInfo, wake_time: u64, state: State) -> u64 {
    let dag_id = dag_info.dag_id;
    let dag = get_dag(dag_id).unwrap_or_else(|| panic!("GEDF scheduler: DAG {dag_id} not found"));

    // The wake of a preempted task resumes it and does not release a job. Any other wake
    // of the source node at an unreleased job must come from its `Interval` tick. After the
    // source node finishes a job, it waits only for that tick, because it has no subscriber.
    let release = state != State::Preempted;

    dag.get_or_release_absolute_deadline(to_node_index(dag_info.node_id), release, || {
        // Microseconds, the unit of `awkernel_lib::delay::uptime()`.
        let relative_deadline_us = dag
            .get_sink_relative_deadline()
            .map(|deadline| deadline.as_micros() as u64)
            .unwrap_or_else(|| {
                panic!("GEDF scheduler: DAG {dag_id} has no sink relative deadline set")
            });
        wake_time + relative_deadline_us
    })
}
