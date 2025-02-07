//! A scheduler for panicked tasks.
//! Panicked tasks will be the lowest priority.

use super::{Scheduler, SchedulerType, Task};
use crate::{scheduler::get_priority, task::State};
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct PanickedScheduler {
    data: Mutex<Option<PanickedData>>, // Run queue.
    priority: u8,
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

        if let Some(data) = data.as_mut() {
            data.queue.push_back(task);
        } else {
            let mut panicked_data = PanickedData::new();
            panicked_data.queue.push_back(task);
            *data = Some(panicked_data);
        }
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        // Pop a task from the run queue.
        // let data = data.as_mut()?;
        #[allow(clippy::question_mark)]
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

                if task_info.state == State::Preempted {
                    task_info.need_preemption = false;
                }
                task_info.state = State::Running;
                task_info.need_preemption = false;
            }

            return Some(task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::Panicked
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

pub static SCHEDULER: PanickedScheduler = PanickedScheduler {
    data: Mutex::new(None),
    priority: get_priority(SchedulerType::Panicked),
};
