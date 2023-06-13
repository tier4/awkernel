//! A basic round robin scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task;
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct RoundRobinScheduler {
    data: Mutex<Option<RoundRobinData>>, // Run queue.
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

        // Make the state of the task InQueue.
        {
            let mut node = MCSNode::new();
            let mut task_info = task.info.lock(&mut node);

            // If the state is Terminated or InQueue, it must not be enqueued.
            if matches!(
                task_info.state,
                task::State::Terminated | task::State::InQueue
            ) {
                return;
            }

            // The task is in the run queue or a preempted task.
            task_info.state = task::State::InQueue;
        }

        data.queue.push_back(task);
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        // Pop a task from the run queue.
        let data = data.as_mut()?;
        let task = data.queue.pop_front()?;

        // Make the state of the task Running.
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
    data: Mutex::new(None),
};
