use alloc::sync::Arc;
use awkernel_lib::sync::mutex::Mutex;

use crate::task::TaskList;

use super::{Scheduler, SchedulerType, Task};

pub struct PrioritizedRoundRobinScheduler {
    data: Mutex<Option<PrioritizedRoundRobinData>>, // Run queue.
}

struct PrioritizedRoundRobinData {
    queue: TaskList,
}

impl PrioritizedRoundRobinData {
    fn new() -> Self {
        Self {
            queue: TaskList::new(),
        }
    }
}

impl Scheduler for PrioritizedRoundRobinScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        todo!()
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        todo!()
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::PrioritizedRoundRobin
    }
}

pub static SCHEDULER: PrioritizedRoundRobinScheduler = PrioritizedRoundRobinScheduler {
    data: Mutex::new(None),
};
