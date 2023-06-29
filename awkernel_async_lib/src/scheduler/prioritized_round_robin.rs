//! A prioritized round robin scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task;
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct PrioritizedRoundRobinScheduler {
    data: Mutex<Option<PrioritizedRoundRobinData>>, // Run queue.
}

struct PrioritizedRoundRobinData {
    queue: VecDeque<Arc<Task>>,
}

impl PrioritizedRoundRobinData {
    fn new() -> Self {
        Self {
            queue: VecDeque::new(),
        }
    }
}

impl Scheduler for PrioritizedRoundRobinScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        if data.is_none() {
            *data = Some(PrioritizedRoundRobinData::new());
        }

        let data = data.as_mut().unwrap();

        // Put the state in queue.
        let mut node = MCSNode::new();
        let mut task_info = task.info.lock(&mut node);

        // If the task is in queue or the state is Terminated, it must not be enqueued.
        if task_info.in_queue
            || matches!(
                task_info.state,
                task::State::Terminated | task::State::Panicked
            )
        {
            return;
        }

        data.queue.push_back(task.clone());

        // The task is in queue.
        task_info.in_queue = true;
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        todo!("PrioritizedRoundRobinScheduler::get_next");
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::PrioritizedRoundRobin(0)
    }
}

pub static SCHEDULER: PrioritizedRoundRobinScheduler = PrioritizedRoundRobinScheduler {
    data: Mutex::new(None),
};
