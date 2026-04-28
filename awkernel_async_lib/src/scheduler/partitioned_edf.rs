//! A Partitioned EDF scheduler.

use core::cmp::max;

use super::{Scheduler, SchedulerType, Task};
use crate::{
    scheduler::{
        gedf::calculate_and_update_dag_deadline, get_priority, peek_preemption_pending,
        push_preemption_pending, PartitionedTask, GLOBAL_WAKE_GET_MUTEX,
    },
    task::{
        get_task, get_task_running, set_current_task, set_need_preemption, State, MAX_TASK_PRIORITY,
    },
};
use alloc::{collections::BinaryHeap, sync::Arc};
use awkernel_lib::{
    cpu::{num_cpu, NUM_MAX_CPU},
    sync::mutex::{MCSNode, Mutex},
};

pub struct PartitionedEDFScheduler {
    data: [Mutex<EDFData>; NUM_MAX_CPU], // Run queue.
    priority: u8,
}

struct PartitionedEDFTask {
    task: Arc<Task>,
    absolute_deadline: u64,
    wake_time: u64,
}

impl PartialOrd for PartitionedEDFTask {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for PartitionedEDFTask {
    fn eq(&self, other: &Self) -> bool {
        self.absolute_deadline == other.absolute_deadline && self.wake_time == other.wake_time
    }
}

impl Ord for PartitionedEDFTask {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        match other.absolute_deadline.cmp(&self.absolute_deadline) {
            core::cmp::Ordering::Equal => other.wake_time.cmp(&self.wake_time),
            other => other,
        }
    }
}

impl Eq for PartitionedEDFTask {}

struct EDFData {
    queue: BinaryHeap<PartitionedTask<PartitionedEDFTask>>,
}

impl EDFData {
    const fn new() -> Self {
        Self {
            queue: BinaryHeap::new(),
        }
    }
}

impl Scheduler for PartitionedEDFScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let (wake_time, absolute_deadline) = {
            let mut node_inner = MCSNode::new();
            let mut info = task.info.lock(&mut node_inner);
            let dag_info = info.get_dag_info();
            match info.scheduler_type {
                SchedulerType::PartitionedEDF(relative_deadline, _) => {
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

        let partitioned_core =
            task.partitioned_core.expect("Task has no partitioned core") as usize;
        if partitioned_core >= num_cpu() || partitioned_core == 0 {
            panic!("PartitionedEDF: core {partitioned_core} is out of range");
        }

        let mut node = MCSNode::new();
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);
        if !self.invoke_preemption(task.clone()) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data[partitioned_core].lock(&mut node_inner);
            data.queue.push(PartitionedTask::new(
                PartitionedEDFTask {
                    task: task.clone(),
                    absolute_deadline,
                    wake_time,
                },
                partitioned_core,
            ));
        }
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        let mut node = MCSNode::new();
        let mut data = self.data[cpu_id].lock(&mut node);

        loop {
            let mut entry = data.queue.pop()?;

            // take() decrements the counter; entry then drops with inner == None.
            let Some(edf_task) = entry.take() else {
                continue;
            };

            {
                let mut node = MCSNode::new();
                let mut task_info = edf_task.task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }

                if task_info.state == State::Preempted {
                    task_info.need_preemption = false;
                }
                if execution_ensured {
                    task_info.state = State::Running;
                    set_current_task(awkernel_lib::cpu::cpu_id(), edf_task.task.id);
                }
            }

            return Some(edf_task.task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::PartitionedEDF(0, 0)
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

pub static SCHEDULER: PartitionedEDFScheduler = PartitionedEDFScheduler {
    data: array_macro::array! [ _ => Mutex::new(EDFData::new()); NUM_MAX_CPU ],
    priority: get_priority(SchedulerType::PartitionedEDF(0, 0)),
};

impl PartitionedEDFScheduler {
    fn invoke_preemption(&self, task: Arc<Task>) -> bool {
        let cpu_id = task.partitioned_core.expect("Task has no partitioned core") as usize;

        let task_running = get_task_running(cpu_id);

        // If the task has already been running, preempt is not required.
        if task_running.task_id == task.id || task_running.task_id == 0 {
            return false;
        }

        let task_running = get_task(task_running.task_id);
        let task_pending = peek_preemption_pending(cpu_id);

        let target_task = match (task_running, task_pending) {
            (Some(running), Some(pending)) => max(running, pending),
            (Some(running), None) => running,
            (None, Some(pending)) => pending,
            (None, None) => return false,
        };

        if task > target_task {
            push_preemption_pending(cpu_id, task);
            let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
            set_need_preemption(target_task.id, cpu_id);
            awkernel_lib::interrupt::send_ipi(preempt_irq, cpu_id as u32);

            // NOTE(atsushi421): Currently, preemption is requested regardless of the number of idle CPUs.
            // While this implementation easily prevents priority inversion, it may also cause unnecessary preemption.
            // Therefore, a more sophisticated implementation will be considered in the future.

            return true;
        }

        false
    }
}
