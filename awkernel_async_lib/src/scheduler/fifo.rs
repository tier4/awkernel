//! A basic FIFO scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task::State;
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct FIFOScheduler {
    data: Mutex<Option<FIFOData>>, // Run queue.
}

struct FIFOData {
    queue: VecDeque<Arc<Task>>,
}

impl FIFOData {
    fn new() -> Self {
        Self {
            queue: VecDeque::new(),
        }
    }
}

impl Scheduler for FIFOScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        if let Some(data) = data.as_mut() {
            data.queue.push_back(task);
        } else {
            let mut fifo_data = FIFOData::new();
            fifo_data.queue.push_back(task);
            *data = Some(fifo_data);
        }
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        // Pop a task from the run queue.
        let data = match data.as_mut() {
            Some(data) => data,
            None => return None,
        };

        loop {
            let task = data.queue.pop_front()?;

            // Make the state of the task Running.
            {
                let mut node = MCSNode::new();
                let mut task_info = task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }

                task_info.state = State::Running;
            }

            return Some(task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::FIFO
    }

    fn priority(&self) -> u8 {
        0
    }
}

pub static SCHEDULER: FIFOScheduler = FIFOScheduler {
    data: Mutex::new(None),
};
