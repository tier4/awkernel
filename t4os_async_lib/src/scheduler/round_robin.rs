use super::{Scheduler, SchedulerType, Task};
use crate::task::{self, TaskList};
use alloc::sync::Arc;
use synctools::mcs::{MCSLock, MCSNode};

pub struct RoundRobinScheduler {
    data: MCSLock<Option<RoundRobinData>>, // Run queue.
}

struct RoundRobinData {
    queue: TaskList,
}

impl RoundRobinData {
    fn new() -> Self {
        Self {
            queue: TaskList::new(),
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

            if matches!(
                task_info.state,
                task::State::Terminated | task::State::InQueue
            ) {
                return;
            }

            task_info.state = task::State::InQueue;
        }

        data.queue.push(task);
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = data.as_mut()?;
        let task = data.queue.pop()?;

        {
            let mut node = MCSNode::new();
            let mut task_info = task.info.lock(&mut node);

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
