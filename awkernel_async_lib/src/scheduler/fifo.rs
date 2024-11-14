//! A basic FIFO scheduler.

use core::sync::atomic::{AtomicUsize, Ordering};

use super::{Scheduler, SchedulerType, Task};
use crate::task::{State, TaskList};
use alloc::sync::Arc;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

const NUM_QUEUE: usize = 32;

pub struct FIFOScheduler {
    queue: [crossbeam_queue::SegQueue<Arc<Task>>; NUM_QUEUE],
    num_task: AtomicUsize,
    push_idx: AtomicUsize,
    pop_idx: AtomicUsize,
}

impl Scheduler for FIFOScheduler {
    #[inline]
    fn wake_task(&self, task: Arc<Task>) {
        let idx = self.push_idx.fetch_add(1, Ordering::Relaxed);
        let idx = idx & (NUM_QUEUE - 1);

        let queue = &self.queue[idx];

        queue.push(task);
        self.num_task
            .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
    }

    #[inline]
    fn get_next(&self) -> Option<Arc<Task>> {
        let idx = self.pop_idx.fetch_add(1, Ordering::Relaxed);
        let idx = idx & (NUM_QUEUE - 1);

        {
            let queue = &self.queue[idx];

            loop {
                let Some(task) = queue.pop() else { break };
                self.num_task.fetch_sub(1, Ordering::Relaxed);

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

        // Work-stealing.
        let mut idx = idx + 1;

        while self.num_task.load(Ordering::Relaxed) > 0 {
            idx = idx & (NUM_QUEUE - 1);

            let queue = &self.queue[idx];

            loop {
                let Some(task) = queue.pop() else { break };
                self.num_task.fetch_sub(1, Ordering::Relaxed);

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

            idx += 1;
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
    queue: array_macro::array![_ => crossbeam_queue::SegQueue::<Arc<Task>>::new(); NUM_QUEUE],
    num_task: AtomicUsize::new(0),
    push_idx: AtomicUsize::new(0),
    pop_idx: AtomicUsize::new(0),
};
