//! A GEDF scheduler.

use core::cmp::max;

use super::{Scheduler, SchedulerType, Task};
use crate::{
    dag::{get_dag, get_dag_absolute_deadline, set_dag_absolute_deadline, to_node_index},
    scheduler::GLOBAL_WAKE_GET_MUTEX,
    scheduler::{get_priority, peek_preemption_pending, push_preemption_pending},
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
                        calculate_and_update_dag_deadline(dag_info, wake_time)
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
    priority: get_priority(SchedulerType::GEDF(0)),
};

impl GEDFScheduler {
    fn invoke_preemption(&self, task: Arc<Task>) -> bool {
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
        if task > target_task {
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

fn get_dag_sink_relative_deadline_ms(dag_id: u32) -> u64 {
    let dag = get_dag(dag_id).unwrap_or_else(|| panic!("GEDF scheduler: DAG {dag_id} not found"));
    dag.get_sink_relative_deadline()
        .map(|deadline| deadline.as_millis() as u64)
        .unwrap_or_else(|| panic!("GEDF scheduler: DAG {dag_id} has no sink relative deadline set"))
}

fn calculate_and_set_dag_deadline(dag_id: u32, wake_time: u64) -> u64 {
    let relative_deadline_ms = get_dag_sink_relative_deadline_ms(dag_id);
    let dag_absolute_deadline = wake_time + relative_deadline_ms;
    set_dag_absolute_deadline(dag_id, dag_absolute_deadline);
    log::debug!("Set DAG {} absolute deadline to {}", dag_id, dag_absolute_deadline);
    dag_absolute_deadline
}

pub fn calculate_and_update_dag_deadline(dag_info: &DagInfo, wake_time: u64) -> u64 {
    let dag_id = dag_info.dag_id;
    let node_id = dag_info.node_id;

    if let Some(absolute_deadline) = get_dag_absolute_deadline(dag_id) {
        let dag =
            get_dag(dag_id).unwrap_or_else(|| panic!("GEDF scheduler: DAG {dag_id} not found"));
        let current_node_index = to_node_index(node_id);
        if !dag.is_source_node(current_node_index) {
            return absolute_deadline;
        }

        // log::info!("DAG {} source node {} wakes up again, recalculate deadline", dag_id, node_id);
        return calculate_and_set_dag_deadline(dag_id, wake_time);
    }

    // log::info!("first time to calculate DAG deadline");
    calculate_and_set_dag_deadline(dag_id, wake_time)
}
