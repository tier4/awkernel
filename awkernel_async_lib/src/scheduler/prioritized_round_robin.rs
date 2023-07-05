//! A prioritized round robin scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task;
use alloc::{collections::VecDeque, sync::Arc, vec::Vec};
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
        let task_info = task.info.lock(&mut node);

        // If the task is in queue or the state is Terminated, it must not be enqueued.
        if task_info.in_queue
            || matches!(
                task_info.state,
                task::State::Terminated | task::State::Panicked
            )
        {
            return;
        }

        drop(task_info);
        insert_into_sorted_queue(&mut data.queue, task.clone());

        // The task is in queue.
        let mut node = MCSNode::new();
        let mut task_info = task.info.lock(&mut node);

        task_info.in_queue = true;
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = data.as_mut()?;

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

/// The tasks with lower numeric priority values are considered higher in priority (with 0 being the highest).
/// If the new task's priority is lower than all existing tasks, it will be added to the end.
fn insert_into_sorted_queue(data_queue: &mut VecDeque<Arc<Task>>, new_task: Arc<Task>) {
    let new_priority = get_priority(&new_task);

    let index = data_queue
        .iter()
        .position(|task| get_priority(task) < new_priority)
        .unwrap_or_else(|| data_queue.len());

    data_queue.insert(index, new_task.clone());
}

fn get_priority(task: &Arc<Task>) -> u8 {
    let mut node = MCSNode::new();
    let task_info = task.info.lock(&mut node);

    match task_info.scheduler_type {
        SchedulerType::PrioritizedRoundRobin(priority) => priority,
        _ => unreachable!(),
    }
}
