//! A basic RR scheduler

use super::{Scheduler, SchedulerType, Task};
use crate::task::{get_last_executed_by_task_id, set_need_preemption, State};
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct RRScheduler {
    // Time quantum
    interval: u64,

    // Priority of this scheduler
    priority: u8,

    // Run queue
    data: Mutex<Option<RRData>>,
}

struct RRData {
    queue: VecDeque<Arc<Task>>,
}

impl RRData {
    fn new() -> Self {
        Self {
            queue: VecDeque::new(),
        }
    }
}

impl Scheduler for RRScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut guard = self.data.lock(&mut node);

        let data = guard.get_or_insert_with(RRData::new);
        data.queue.push_back(task.clone());
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut guard = self.data.lock(&mut node);

        let data = match guard.as_mut() {
            Some(d) => d,
            None => return None,
        };

        while let Some(task) = data.queue.pop_front() {
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

        None
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::RR
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

pub static SCHEDULER: RRScheduler = RRScheduler {
    // Time quantum (100 ms)
    interval: 100_000,

    // TODO: Temporarily set to the lowest priority
    priority: 16,

    data: Mutex::new(None),
};

impl RRScheduler {
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
