//! A Priority Based RR scheduler

use super::{Scheduler, SchedulerType, Task};
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::Mutex;

pub struct PriorityBasedRRScheduler {
    // Run queue
    _data: Mutex<Option<PriorityBasedRRData>>,
}

struct PriorityBasedRRData {
    _queue: VecDeque<Arc<Task>>,
}

impl PriorityBasedRRData {
    fn _new() -> Self {
        Self {
            _queue: VecDeque::new(),
        }
    }
}

impl Scheduler for PriorityBasedRRScheduler {
    fn wake_task(&self, _task: Arc<Task>) {
        // TODO: implement
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        // TODO: implement
        None
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::PriorityBasedRR
    }

    fn priority(&self) -> u8 {
        0
    }
}

pub static SCHEDULER: PriorityBasedRRScheduler = PriorityBasedRRScheduler {
    _data: Mutex::new(None),
};
