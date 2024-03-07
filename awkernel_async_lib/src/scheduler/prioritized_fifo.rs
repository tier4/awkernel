//! A prioritized round robin scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task::State;
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct PrioritizedFIFOScheduler {
    data: Mutex<Option<PrioritizedFIFOData>>, // Run queue.
}

struct PrioritizedFIFOData {
    queue: VecDeque<Arc<Task>>,
}

impl PrioritizedFIFOData {
    fn new() -> Self {
        Self {
            queue: VecDeque::new(),
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

        // Put the state in queue.
        insert_in_priority_order(&mut data.queue, task.clone());
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = data.as_mut()?;

        loop {
            // Pop a task from the run queue.
            let task = data.queue.pop_front()?;

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
        SchedulerType::PrioritizedFIFO(0)
    }
}

pub static SCHEDULER: PrioritizedFIFOScheduler = PrioritizedFIFOScheduler {
    data: Mutex::new(None),
};

fn insert_in_priority_order(data_queue: &mut VecDeque<Arc<Task>>, new_task: Arc<Task>) {
    let new_priority = get_priority(&new_task);

    let index = data_queue
        .iter()
        .position(|task| get_priority(task) < new_priority)
        .unwrap_or(data_queue.len());

    data_queue.insert(index, new_task);
}

fn get_priority(task: &Arc<Task>) -> u8 {
    let mut node = MCSNode::new();
    let task_info = task.info.lock(&mut node);

    match task_info.scheduler_type {
        SchedulerType::PrioritizedFIFO(priority) => priority,
        _ => unreachable!(),
    }
}
