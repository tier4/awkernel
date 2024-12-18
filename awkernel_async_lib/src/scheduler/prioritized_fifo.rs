//! A prioritized FIFO scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::{scheduler::get_priority, task::State};
use alloc::sync::Arc;
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
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        if let Some(data) = data.as_mut() {
            let mut node = MCSNode::new();
            let info = task.info.lock(&mut node);
            let SchedulerType::PrioritizedFIFO(priority) = info.scheduler_type else {
                return;
            };

            data.queue.push(
                priority as u32,
                PrioritizedFIFOTask {
                    task: task.clone(),
                    _priority: priority,
                },
            );
        } else {
            let mut prioritized_fifo_data = PrioritizedFIFOData::new();
            let mut node = MCSNode::new();
            let info = task.info.lock(&mut node);
            let SchedulerType::PrioritizedFIFO(priority) = info.scheduler_type else {
                return;
            };

            prioritized_fifo_data.queue.push(
                priority as u32,
                PrioritizedFIFOTask {
                    task: task.clone(),
                    _priority: priority,
                },
            );
            *data = Some(prioritized_fifo_data);
        }
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

pub static SCHEDULER: PrioritizedFIFOScheduler = PrioritizedFIFOScheduler {
    data: Mutex::new(None),
    priority: get_priority(SchedulerType::PrioritizedFIFO(0)),
};
