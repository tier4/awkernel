//! A Priority Based RR scheduler

use super::{Scheduler, SchedulerType, Task};
use crate::task::{get_last_executed_by_task_id, set_need_preemption};
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::Mutex;

pub struct PriorityBasedRRScheduler {
    // Time quantum
    interval: u64,

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
    // Time quantum (100 ms)
    interval: 100_000,

    _data: Mutex::new(None),
};

impl PriorityBasedRRScheduler {
    // Invoke a preemption if the task exceeds the time quantum
    pub fn invoke_preemption(&self, cpu_id: usize, task_id: u32) {
        let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
        if let Some(last_executed) = get_last_executed_by_task_id(task_id) {
            let elapsed = awkernel_lib::delay::uptime() - last_executed;
            if last_executed != 0 && elapsed > self.interval {
                set_need_preemption(task_id);
                awkernel_lib::interrupt::send_ipi(preempt_irq, cpu_id as u32);
            }
        }
    }
}
