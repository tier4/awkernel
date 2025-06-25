//! A prioritized FIFO scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task::{get_scheduler_type_by_task_id, get_tasks_running, set_need_preemption};
use crate::{scheduler::get_priority, task::State};
use alloc::sync::Arc;
use alloc::vec::Vec;
use awkernel_lib::cpu::num_cpu;
use awkernel_lib::priority_queue::PriorityQueue;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct PrioritizedFIFOScheduler {
    data: Mutex<Option<PrioritizedFIFOData>>, // Run queue.
    priority: u8,
}

struct PrioritizedFIFOTask {
    task: Arc<Task>,
    _priority: u8,
}

struct PrioritizedFIFOData {
    queue: PriorityQueue<PrioritizedFIFOTask>,
}

impl PrioritizedFIFOData {
    fn new() -> Self {
        Self {
            queue: PriorityQueue::new(),
        }
    }
}

impl Scheduler for PrioritizedFIFOScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let priority = {
            let mut node = MCSNode::new();
            let info = task.info.lock(&mut node);
            match info.scheduler_type {
                SchedulerType::PrioritizedFIFO(p) => p,
                _ => unreachable!(),
            }
        };

        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);
        let internal_data = data.get_or_insert_with(PrioritizedFIFOData::new);
        internal_data.queue.push(
            priority as u32,
            PrioritizedFIFOTask {
                task: task.clone(),
                _priority: priority,
            },
        );

        self.invoke_preemption(priority);
    }

    fn get_next(&self) -> Option<Arc<Task>> {
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
                task_info.state = State::Running;
            }

            return Some(task.task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::PrioritizedFIFO(0)
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

impl PrioritizedFIFOScheduler {
    fn invoke_preemption(&self, priority: u8) {
        let tasks_running = get_tasks_running()
            .into_iter()
            .filter(|task| task.task_id != 0)
            .collect::<Vec<_>>();

        // If the number of running tasks is less than the number of non-primary CPUs, preempt is not required.
        if tasks_running.len() < num_cpu() - 1 {
            return;
        }

        let lowest_priority_running_task = tasks_running
            .iter()
            .filter_map(|task| {
                get_scheduler_type_by_task_id(task.task_id).and_then(|scheduler_type| {
                    match scheduler_type {
                        SchedulerType::PrioritizedFIFO(p) => Some((task, p)),
                        _ => None, // TODO: Inter-scheduler preemption is not supported yet.
                    }
                })
            })
            .max_by_key(|(_, p)| *p);

        if let Some((task, lowest_priority)) = lowest_priority_running_task {
            if priority < lowest_priority {
                let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
                set_need_preemption(task.task_id, task.cpu_id);
                awkernel_lib::interrupt::send_ipi(preempt_irq, task.cpu_id as u32);
            }
        }
    }
}

pub static SCHEDULER: PrioritizedFIFOScheduler = PrioritizedFIFOScheduler {
    data: Mutex::new(None),
    priority: get_priority(SchedulerType::PrioritizedFIFO(0)),
};
