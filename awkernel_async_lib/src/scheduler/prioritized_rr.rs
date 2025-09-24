//! A Priority Based RR scheduler

use core::cmp::max;

use super::{Scheduler, SchedulerType, Task};
use crate::{
    scheduler::{
        get_next_task, get_priority, peek_preemption_pending, push_preemption_pending,
        GLOBAL_WAKE_GET_MUTEX,
    },
    task::{
        get_last_executed_by_task_id, get_task, get_tasks_running, set_current_task,
        set_need_preemption, State,
    },
};
use alloc::{sync::Arc, vec::Vec};
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
        let priority = {
            let mut node_inner = MCSNode::new();
            let info = task.info.lock(&mut node_inner);
            match info.scheduler_type {
                SchedulerType::PrioritizedRR(p) => p,
                _ => unreachable!(),
            }
        };

        let mut node = MCSNode::new();
        GLOBAL_WAKE_GET_MUTEX.lock(&mut node);
        if !self.invoke_preemption_wake(task.clone()) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data.lock(&mut node_inner);
            let internal_data = data.get_or_insert_with(PrioritizedRRData::new);
            internal_data.queue.push(
                priority,
                PrioritizedRRTask {
                    task: task.clone(),
                    _priority: priority,
                },
            );
        }
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        GLOBAL_WAKE_GET_MUTEX.lock(&mut node);

        let mut node_inner = MCSNode::new();
        let mut guard = self.data.lock(&mut node_inner);

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
                if execution_ensured {
                    task_info.state = State::Running;
                    set_current_task(awkernel_lib::cpu::cpu_id(), rr_task.task.id);
                }
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
    pub fn invoke_preemption_tick(&self, cpu_id: usize, task_id: u32) {
        if let Some(last_executed) = get_last_executed_by_task_id(task_id) {
            let elapsed = last_executed.elapsed().as_micros() as u64;
            if elapsed > self.interval {
                if let Some(next_task) = get_next_task(false) {
                    push_preemption_pending(cpu_id, next_task);
                    let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
                    set_need_preemption(task_id, cpu_id);
                    awkernel_lib::interrupt::send_ipi(preempt_irq, cpu_id as u32);
                }
            }
        }
    }

    fn invoke_preemption_wake(&self, task: Arc<Task>) -> bool {
        let tasks_running = get_tasks_running()
            .into_iter()
            .filter(|rt| rt.task_id != 0) // Filter out idle CPUs
            .collect::<Vec<_>>();

        // If the task has already been running, preempt is not required.
        if tasks_running.is_empty() || tasks_running.iter().any(|rt| rt.task_id == task.id) {
            return false;
        }

        let preemption_target = tasks_running
            .iter()
            .filter_map(|rt| {
                get_task(rt.task_id).map(|t| {
                    let highest_pending = peek_preemption_pending(rt.cpu_id).unwrap_or(t.clone());
                    (max(t, highest_pending), rt.cpu_id)
                })
            })
            .min()
            .unwrap();

        let (target_task, target_cpu) = preemption_target;
        if task > target_task {
            push_preemption_pending(target_cpu, task);
            let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
            set_need_preemption(target_task.id, target_cpu);
            awkernel_lib::interrupt::send_ipi(preempt_irq, target_cpu as u32);

            // NOTE(atsushi421): Currently, preemption is requested regardless of the number of idle CPUs.
            // While this implementation easily prevents priority inversion, it may also cause unnecessary preemption.
            // Therefore, a more sophisticated implementation will be considered in the future.

            return true;
        }

        false
    }
}
