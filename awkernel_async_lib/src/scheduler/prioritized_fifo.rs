//! A prioritized round robin scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task::State;
use alloc::{collections::BinaryHeap, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct PrioritizedFIFOScheduler {
    data: Mutex<Option<PrioritizedFIFOData>>, // Run queue.
}

struct PrioritizedFIFOTask {
    task: Arc<Task>,
    priority: u8,
}

impl PartialOrd for PrioritizedFIFOTask {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for PrioritizedFIFOTask {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl Ord for PrioritizedFIFOTask {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.priority.cmp(&other.priority).reverse()
    }
}

impl Eq for PrioritizedFIFOTask {}

struct PrioritizedFIFOData {
    queue: BinaryHeap<PrioritizedFIFOTask>,
}

impl PrioritizedFIFOData {
    fn new() -> Self {
        Self {
            queue: BinaryHeap::new(),
        }
    }
}

impl Scheduler for PrioritizedFIFOScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        if data.is_none() {
            *data = Some(PrioritizedFIFOData::new());
        }

        let data = data.as_mut().unwrap();

        let mut node = MCSNode::new();
        let info = task.info.lock(&mut node);
        let SchedulerType::PrioritizedFIFO(priority) = info.scheduler_type else {
            return;
        };

        data.queue.push(PrioritizedFIFOTask {
            task: task.clone(),
            priority,
        });
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = data.as_mut()?;

        loop {
            // Pop a task from the run queue.
            let task = data.queue.pop()?;

            // Make the state of the task Running.
            {
                let mut node = MCSNode::new();
                let mut task_info = task.task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }

                task_info.state = State::Running;
            }

            return Some(task.task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::PrioritizedFIFO(0)
    }

    fn priority(&self) -> u8 {
        0
    }
}

pub static SCHEDULER: PrioritizedFIFOScheduler = PrioritizedFIFOScheduler {
    data: Mutex::new(None),
};
