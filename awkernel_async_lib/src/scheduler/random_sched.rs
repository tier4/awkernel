//! A random scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task;
use alloc::{sync::Arc, vec::Vec};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

/// The random scheduler instance.
pub static SCHEDULER: RandomScheduler = RandomScheduler {
    data: Mutex::new(None),
};

pub struct RandomScheduler {
    data: Mutex<Option<RandomSchedulerData>>,
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

        // Generate a random number.
        let key = loop {
            let key = data.rnd.random() as usize & (N - 1);
            if data.tasks[key].is_none() {
                break key;
            }
        };

        // Make the state of the task InQueue.
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

        data.tasks[key] = Some(task.clone());

        // The task is in queue.
        task_info.in_queue = true;
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

        // Make the task not in queue.
        {
            let mut node = MCSNode::new();
            let mut task_info = task.info.lock(&mut node);
            task_info.in_queue = false;
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
