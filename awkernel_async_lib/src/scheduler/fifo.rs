//! A basic FIFO scheduler.

use core::sync::atomic::{AtomicUsize, Ordering};

use super::{Scheduler, SchedulerType, Task};
use crate::task::{State, TaskList};
use alloc::sync::Arc;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

const NUM_FIFO: usize = 32;

pub struct FIFOScheduler {
    data: [Mutex<Option<FIFOData>>; NUM_FIFO], // Run queue.
    next_push: AtomicUsize,
    next_pop: AtomicUsize,
    num_tasks: AtomicUsize,
}

struct FIFOData {
    queue: TaskList,
}

impl FIFOData {
    fn new() -> Self {
        Self {
            queue: TaskList::new(),
        }
    }
}

impl Scheduler for FIFOScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let idx = self.next_push.fetch_add(1, Ordering::Relaxed) & (NUM_FIFO - 1);

        let mut node = MCSNode::new();
        let mut data = self.data[idx].lock(&mut node);

        if let Some(data) = data.as_mut() {
            data.queue.push_back(task);
        } else {
            let mut fifo_data = FIFOData::new();
            fifo_data.queue.push_back(task);
            *data = Some(fifo_data);
        }

        self.num_tasks.fetch_add(1, Ordering::Relaxed);
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        while self.num_tasks.load(Ordering::Relaxed) > 0 {
            let idx = self.next_pop.fetch_add(1, Ordering::Relaxed) & (NUM_FIFO - 1);

            let mut node = MCSNode::new();
            let mut data = self.data[idx].lock(&mut node);

            // Pop a task from the run queue.
            let data = match data.as_mut() {
                Some(data) => data,
                None => continue,
            };

            loop {
                let task = data.queue.pop_front()?;
                self.num_tasks.fetch_sub(1, Ordering::Relaxed);

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

        None
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::FIFO
    }

    fn priority(&self) -> u8 {
        0
    }
}

pub static SCHEDULER: FIFOScheduler = FIFOScheduler {
    data: array_macro::array![_ =>  Mutex::new(None); NUM_FIFO],
    next_push: AtomicUsize::new(0),
    next_pop: AtomicUsize::new(0),
    num_tasks: AtomicUsize::new(0),
};
