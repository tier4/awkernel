//! A basic RR scheduler

use super::{Scheduler, SchedulerType, Task};
use crate::task::{get_current_task_ref, get_raw_cpu_id, State};
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
        let mut data = self.data.lock(&mut node);

        if data.is_none() {
            *data = Some(RRData::new());
        }

        let data = data.as_mut().unwrap();

        data.queue.push_back(task.clone());
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = data.as_mut()?;

        loop {
            let task = data.queue.pop_front()?;

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
    /// Checks whether each task is not running beyond the quantum time and preempt if it is
    pub fn check_quantum_time_for_rr_tasks(&self) {
        let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
        for cpu_id in 1..awkernel_lib::cpu::num_cpu() {
            if let Some(task) = get_current_task_ref(cpu_id) {
                let (last_executed, scheduler_type) = {
                    let mut node = MCSNode::new();
                    let info = task.info.lock(&mut node);
                    (info.get_last_executed(), info.get_scheduler_type())
                };

                let current_time = awkernel_lib::delay::uptime();
                let running_time = current_time - last_executed;

                if scheduler_type == SchedulerType::RR
                    // Omits checking for a task that has not been started yet
                    && last_executed != 0
                    // Checks whether the quantum time is exceeded
                    && running_time > self.interval
                {
                    awkernel_lib::interrupt::send_ipi(preempt_irq, get_raw_cpu_id(cpu_id) as u32);
                }
            }
        }
    }
}
