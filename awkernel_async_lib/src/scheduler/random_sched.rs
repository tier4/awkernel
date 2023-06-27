//! A random scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task;
use alloc::{sync::Arc, vec::Vec};
use synctools::mcs::{MCSLock, MCSNode};

/// The random scheduler instance.
pub static SCHEDULER: RandomScheduler = RandomScheduler {
    data: MCSLock::new(None),
};

pub struct RandomScheduler {
    data: MCSLock<Option<RandomSchedulerData>>,
}

const N: usize = 0x100;

struct RandomSchedulerData {
    tasks: Vec<Option<Arc<Task>>>,
    rnd: RND,
}

impl RandomSchedulerData {
    fn new() -> Self {
        let mut tasks = Vec::with_capacity(N);
        for _ in 0..N {
            tasks.push(None);
        }

        Self {
            tasks,
            rnd: RND::new(),
        }
    }
}

impl Scheduler for RandomScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        if data.is_none() {
            *data = Some(RandomSchedulerData::new());
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

            // The task is in the run queue.
            task_info.state = task::State::InQueue;
        }

        // Generate a random number.
        let key = loop {
            let key = data.rnd.random() as usize & (N - 1);
            if data.tasks[key].is_none() {
                break key;
            }
        };

        data.tasks[key] = Some(task);
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = data.as_mut()?;

        // Pick a task up randomly.
        let offset = data.rnd.random() as usize & (N - 1);
        let mut i = 0;
        let task = loop {
            if i == N {
                return None;
            }

            if let Some(task) = data.tasks[(i + offset) & (N - 1)].take() {
                break task;
            }

            i += 1;
        };

        // Make the state of the task Running.
        {
            let mut node = MCSNode::new();
            let mut task_info = task.info.lock(&mut node);

            task_info.state = task::State::Running;
        }

        Some(task)
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::Random
    }
}

struct RND {
    x: u32,
}

impl RND {
    const fn new() -> Self {
        RND { x: 123 }
    }

    fn random(&mut self) -> u32 {
        if self.x == 0 {
            self.x = 123;
        }

        let x = (self.x as u64 * 48271) + 1013904223;
        self.x = (x & ((1 << 31) - 1)) as u32;
        self.x
    }
}
