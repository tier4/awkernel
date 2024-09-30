//! A basic RR scheduler

use super::{Scheduler, SchedulerType, Task};
use crate::task::{
    get_current_task, get_last_executed_by_task_id, get_raw_cpu_id, get_scheduler_type_by_task_id,
    set_need_preemption, State,
};
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::{
    cpu::num_cpu,
    sync::mutex::{MCSNode, Mutex},
};

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
    /// Check whether each running task does not exceed the time quantum
    pub fn check_time_quantum(&self) {
        let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();

        for cpu_id in 1..num_cpu() {
            if let Some(task_id) = get_current_task(cpu_id) {
                if let (Some(last_executed), Some(scheduler_type)) = (
                    get_last_executed_by_task_id(task_id),
                    get_scheduler_type_by_task_id(task_id),
                ) {
                    let elapsed = awkernel_lib::delay::uptime() - last_executed;

                    if scheduler_type == SchedulerType::RR
                            // Omit checking for a task that has not been started yet
                            && last_executed != 0
                            // Compare the elapsed time with the time quantum 
                            && elapsed > self.interval
                    {
                        set_need_preemption(task_id);

                        awkernel_lib::interrupt::send_ipi(
                            preempt_irq,
                            get_raw_cpu_id(cpu_id) as u32,
                        );
                    }
                }
            }
        }
    }
}
