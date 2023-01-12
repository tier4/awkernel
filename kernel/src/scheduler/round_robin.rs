use super::{Scheduler, SchedulerType, Task};
use crate::task;
use alloc::{collections::VecDeque, sync::Arc};
use synctools::mcs::{MCSLock, MCSNode};

const QUEUE_SIZE: usize = 1024 * 1024;

pub struct RoundRobinScheduler {
    data: MCSLock<Option<RoundRobinData>>, // Run queue.
}

struct RoundRobinData {
    queue: VecDeque<Arc<Task>>,
}

impl RoundRobinData {
    fn new() -> Self {
        Self {
            queue: VecDeque::new(),
        }
    }
}

impl Scheduler for RoundRobinScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        if data.is_none() {
            *data = Some(RoundRobinData::new());
        }

        let data = data.as_mut().unwrap();

        {
            let mut node = MCSNode::new();
            let mut task_info = task.info.lock(&mut node);

            if matches!(task_info.state, task::State::Finished) || task_info.in_queue {
                return;
            }

            task_info.in_queue = true;
        }

        data.queue.push_back(task);
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = data.as_mut()?;
        let task = data.queue.pop_front()?;

        {
            let mut node = MCSNode::new();
            let mut task_info = task.info.lock(&mut node);

            task_info.in_queue = false;
            task_info.state = task::State::Running;
        }

        Some(task)
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::RoundRobin
    }
}

pub static SCHEDULER: RoundRobinScheduler = RoundRobinScheduler {
    data: MCSLock::new(None),
};
