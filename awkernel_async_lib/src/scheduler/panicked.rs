//! A scheduler for panicked tasks.
//! Panicked tasks will be the lowest priority.

use super::{Scheduler, SchedulerType, Task};
use crate::task::State;
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct PanickedScheduler {
    data: Mutex<Option<PanickedData>>, // Run queue.
}

struct PanickedData {
    queue: VecDeque<Arc<Task>>,
}

impl PanickedData {
    fn new() -> Self {
        Self {
            queue: VecDeque::new(),
        }
    }
}

impl Scheduler for PanickedScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        if data.is_none() {
            *data = Some(PanickedData::new());
        }

        let data = data.as_mut().unwrap();

        // Put the state in queue.
        data.queue.push_back(task.clone());
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        // Pop a task from the run queue.
        let data = data.as_mut()?;

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
}

pub static SCHEDULER: PanickedScheduler = PanickedScheduler {
    data: Mutex::new(None),
};
