use super::{Scheduler, SchedulerType, Task};
use alloc::{collections::VecDeque, sync::Arc};
use synctools::mcs::{MCSLock, MCSNode};

pub struct RoundRobinScheduler {
    queue: MCSLock<Option<VecDeque<Arc<Task>>>>, // Run queue.
}

impl Scheduler for RoundRobinScheduler {
    fn wake_task(&self, task: Arc<super::Task>) {
        let mut node = MCSNode::new();
        let mut guard = self.queue.lock(&mut node);

        if guard.is_none() {
            *guard = Some(VecDeque::new());
        }

        let q = guard.as_mut().unwrap();
        q.push_back(task);
    }

    fn get_next(&self) -> Option<Arc<super::Task>> {
        let mut node = MCSNode::new();
        let mut guard = self.queue.lock(&mut node);

        let q = guard.as_mut()?;
        q.pop_front()
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::RoundRobin
    }
}

pub static SCHEDULER: RoundRobinScheduler = RoundRobinScheduler {
    queue: MCSLock::new(None),
};
