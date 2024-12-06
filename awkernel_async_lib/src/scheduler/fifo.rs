//! A basic FIFO scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::{task::State, scheduler::get_priority};
use alloc::{collections::vec_deque::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct FIFOScheduler {
    queue: Mutex<Option<VecDeque<Arc<Task>>>>, // Run queue.
    priority: u8,
}

impl Scheduler for FIFOScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut queue = self.queue.lock(&mut node);

        if let Some(queue) = queue.as_mut() {
            queue.push_back(task);
        } else {
            let mut q = VecDeque::new();
            q.push_back(task);
            *queue = Some(q);
        }
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut queue = self.queue.lock(&mut node);

        // Pop a task from the run queue.
        #[allow(clippy::question_mark)]
        let queue = match queue.as_mut() {
            Some(q) => q,
            None => return None,
        };

        loop {
            let task = queue.pop_front()?;

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
        self.priority
    }
}

pub static SCHEDULER: FIFOScheduler = FIFOScheduler {
    queue: Mutex::new(None),
    priority: get_priority(SchedulerType::FIFO),
};
