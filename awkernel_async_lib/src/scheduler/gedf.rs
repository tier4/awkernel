//! A GEDF scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task::State;
use alloc::{collections::BinaryHeap, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct GEDFScheduler {
    data: Mutex<Option<GEDFData>>, // Run queue.
}

struct GEDFTask {
    task: Arc<Task>,
    priority: u8,
}

impl PartialOrd for GEDFTask {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for GEDFTask {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl Ord for GEDFTask {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.priority.cmp(&other.priority).reverse()
    }
}

impl Eq for GEDFTask {}

struct GEDFData {
    queue: BinaryHeap<GEDFTask>,
}

impl GEDFData {
    fn new() -> Self {
        Self {
            queue: BinaryHeap::new(),
        }
    }
}

impl Scheduler for GEDFScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        if let Some(data) = data.as_mut() {
            let mut node = MCSNode::new();
            let info = task.info.lock(&mut node);
            let SchedulerType::GEDF(priority) = info.scheduler_type else {
                return;
            };

            data.queue.push(GEDFTask {
                task: task.clone(),
                priority,
            });
        } else {
            let mut prioritized_fifo_data = GEDFData::new();
            let mut node = MCSNode::new();
            let info = task.info.lock(&mut node);
            let SchedulerType::GEDF(priority) = info.scheduler_type else {
                return;
            };

            prioritized_fifo_data.queue.push(GEDFTask {
                task: task.clone(),
                priority,
            });
            *data = Some(prioritized_fifo_data);
        }
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = match data.as_mut() {
            Some(data) => data,
            None => return None,
        };

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
        SchedulerType::GEDF(0)
    }

    fn priority(&self) -> u8 {
        0
    }
}

pub static SCHEDULER: GEDFScheduler = GEDFScheduler {
    data: Mutex::new(None),
};
