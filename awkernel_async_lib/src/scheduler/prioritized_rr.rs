//! A Priority Based RR scheduler

use super::{Scheduler, SchedulerType, Task};
use crate::{
    scheduler::get_priority,
    task::{get_last_executed_by_task_id, set_need_preemption, State},
};
use alloc::sync::Arc;
use awkernel_lib::priority_queue::PriorityQueue;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct PrioritizedRRScheduler {
    // Time quantum
    interval: u64,
    data: Mutex<Option<PrioritizedRRData>>,
    priority: u8,
}

struct PrioritizedRRTask {
    task: Arc<Task>,
    _priority: u8,
}

struct PrioritizedRRData {
    queue: PriorityQueue<PrioritizedRRTask>,
}

impl PrioritizedRRData {
    fn new() -> Self {
        Self {
            queue: PriorityQueue::new(),
        }
    }
}

impl Scheduler for PrioritizedRRScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let info = task.info.lock(&mut node);
        let SchedulerType::PrioritizedRR(priority) = info.scheduler_type else {
            return;
        };
        let new_task = PrioritizedRRTask {
            task: task.clone(),
            _priority: priority,
        };

        let mut node = MCSNode::new();
        let mut guard = self.data.lock(&mut node);
        let data = guard.get_or_insert_with(PrioritizedRRData::new);
        data.queue.push(priority, new_task);
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut guard = self.data.lock(&mut node);

        #[allow(clippy::question_mark)]
        let data = match guard.as_mut() {
            Some(data) => data,
            None => return None,
        };

        while let Some(rr_task) = data.queue.pop() {
            {
                let mut node = MCSNode::new();
                let mut task_info = rr_task.task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }

                if task_info.state == State::Preempted {
                    task_info.need_preemption = false;
                }
                task_info.state = State::Running;
            }

            return Some(rr_task.task);
        }

        None
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::PrioritizedRR(0)
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

pub static SCHEDULER: PrioritizedRRScheduler = PrioritizedRRScheduler {
    // Time quantum (4 ms)
    interval: 4_000,
    data: Mutex::new(None),
    priority: get_priority(SchedulerType::PrioritizedRR(0)),
};

impl PrioritizedRRScheduler {
    // Invoke a preemption if the task exceeds the time quantum
    pub fn invoke_preemption(&self, cpu_id: usize, task_id: u32) {
        let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
        if let Some(last_executed) = get_last_executed_by_task_id(task_id) {
            let elapsed = last_executed.elapsed().as_micros() as u64;
            if elapsed > self.interval {
                set_need_preemption(task_id, cpu_id);
                awkernel_lib::interrupt::send_ipi(preempt_irq, cpu_id as u32);
            }
        }
    }
}
