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
    priority: u8,
}

impl PrioritizedRoundRobinData {
    fn new() -> Self {
        Self {
            queue: VecDeque::new(),
            priority: 0,
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

        //Assign priorities in the order in which they become available for execution
        match task_info.scheduler_type {
            SchedulerType::PrioritizedRoundRobin(_) => {
                task_info.scheduler_type = SchedulerType::PrioritizedRoundRobin(data.priority);
                data.priority += 1;
            }
            _ => {
                panic!("The scheduler type of the task is not PrioritizedRoundRobin.")
            }
        }

        data.queue.push_back(task.clone());

        // The task is in queue.
        task_info.in_queue = true;
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = data.as_mut()?;

        // Sort the queue by priority.
        data.queue.make_contiguous().sort_by(|task1, task2| {
            let mut node = MCSNode::new();
            let task1_info = task1.info.lock(&mut node);
            let mut node = MCSNode::new();
            let task2_info = task2.info.lock(&mut node);

            match (task1_info.scheduler_type, task2_info.scheduler_type) {
                (
                    SchedulerType::PrioritizedRoundRobin(priority1),
                    SchedulerType::PrioritizedRoundRobin(priority2),
                ) => priority1.cmp(&priority2),
                _ => {
                    panic!("The scheduler type of the task is not PrioritizedRoundRobin.")
                }
            }
        });

        // Pop a task from the run queue.
        let task = data.queue.pop_front()?;

        // Make the state of the task Running.
        {
            let mut node = MCSNode::new();
            let mut task_info = task.info.lock(&mut node);
            task_info.in_queue = false;
        }

        Some(task)
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::PrioritizedRoundRobin(0)
    }
}

pub static SCHEDULER: PrioritizedRoundRobinScheduler = PrioritizedRoundRobinScheduler {
    data: Mutex::new(None),
};
