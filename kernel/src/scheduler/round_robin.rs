use super::{Scheduler, SchedulerType, Task};
use alloc::{
    collections::{BTreeSet, VecDeque},
    sync::Arc,
};
use synctools::mcs::{MCSLock, MCSNode};

pub struct RoundRobinScheduler {
    data: MCSLock<Option<RoundRobinData>>, // Run queue.
}

#[derive(Default)]
struct RoundRobinData {
    queue: VecDeque<Arc<Task>>,
    in_queue: BTreeSet<u64>,
}

impl Scheduler for RoundRobinScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut guard = self.data.lock(&mut node);

        if guard.is_none() {
            *guard = Some(Default::default());
        }

        let data = guard.as_mut().unwrap();

        if !data.in_queue.contains(&task.get_id()) {
            data.in_queue.insert(task.get_id());
            data.queue.push_back(task);
        }
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut guard = self.data.lock(&mut node);

        let data = guard.as_mut()?;
        let task = data.queue.pop_front()?;

        data.in_queue.remove(&task.get_id());

        Some(task)
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::RoundRobin
    }
}

pub static SCHEDULER: RoundRobinScheduler = RoundRobinScheduler {
    data: MCSLock::new(None),
};
