//! A scheduler for panicked tasks.
//! Panicked tasks will be the lowest priority.

use super::{Scheduler, SchedulerType, Task};
use crate::{
    scheduler::get_priority,
    task::{set_current_task, State, NUM_TASK_IN_QUEUE},
};
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::sync::atomic::Ordering;

pub struct PanickedScheduler {
    data: Mutex<Option<PanickedData>>, // Run queue.
    priority: u8,
}

struct PanickedData {
    queue: VecDeque<Arc<Task>>,
}

impl PanickedData {
    fn new() -> Self {
        Self {
            queue: VecDeque::new(),
        }
    }
}

impl Scheduler for PanickedScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        data.get_or_insert_with(PanickedData::new)
            .queue
            .push_back(task);
        NUM_TASK_IN_QUEUE.fetch_add(1, Ordering::Relaxed);
        drop(data);

        // `do_preemption` and `run_main` re-wake tasks through this function
        // without `ArcWake::wake`, so notify the primary CPU here to wake an
        // idle worker.
        awkernel_lib::cpu::wake_cpu(0);
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        // Pop a task from the run queue.
        // let data = data.as_mut()?;
        #[allow(clippy::question_mark)]
        let data = match data.as_mut() {
            Some(data) => data,
            None => return None,
        };

        loop {
            let task = data.queue.pop_front()?;
            NUM_TASK_IN_QUEUE.fetch_sub(1, Ordering::Relaxed);

            // Make the state of the task Running.
            {
                let mut node = MCSNode::new();
                let mut task_info = task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }

                if task_info.state == State::Preempted {
                    task_info.need_preemption = false;
                }
                if execution_ensured {
                    task_info.state = State::Running;
                    set_current_task(awkernel_lib::cpu::cpu_id(), task.id);
                }
            }

            return Some(task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::Panicked
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

pub static SCHEDULER: PanickedScheduler = PanickedScheduler {
    data: Mutex::new(None),
    priority: get_priority(&SchedulerType::Panicked),
};
