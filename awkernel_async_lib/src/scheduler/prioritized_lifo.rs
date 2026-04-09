//! A prioritized LIFO scheduler.

use core::cmp::max;

use super::{Scheduler, SchedulerType, Task};
use crate::scheduler::{peek_preemption_pending, push_preemption_pending, GLOBAL_WAKE_GET_MUTEX};
use crate::task::{get_task, get_tasks_running, set_current_task, set_need_preemption};
use crate::{scheduler::get_priority, task::State};
use alloc::collections::VecDeque;
use alloc::sync::Arc;
use alloc::vec::Vec;
use array_macro::array;
use awkernel_lib::priority_queue::HIGHEST_PRIORITY;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct PrioritizedLIFOScheduler {
    data: Mutex<Option<PrioritizedLIFOData>>, // Run queue.
    priority: u8,
}

struct PrioritizedLIFOTask {
    task: Arc<Task>,
    _priority: u8,
}

struct PrioritizedLIFOData {
    queues: [VecDeque<PrioritizedLIFOTask>; HIGHEST_PRIORITY as usize + 1],
    has_entry: u32,
}

impl PrioritizedLIFOData {
    fn new() -> Self {
        Self {
            queues: array![_ => VecDeque::new(); HIGHEST_PRIORITY as usize + 1],
            has_entry: 0,
        }
    }

    fn push(&mut self, priority: u8, val: PrioritizedLIFOTask) {
        let priority = priority.min(HIGHEST_PRIORITY);
        let queue = &mut self.queues[priority as usize];
        queue.push_back(val);
        self.has_entry |= 1 << priority;
    }

    fn pop(&mut self) -> Option<PrioritizedLIFOTask> {
        if self.has_entry == 0 {
            return None;
        }

        let next_priority = (u32::BITS - 1) - self.has_entry.leading_zeros();
        let queue = &mut self.queues[next_priority as usize];
        let next = queue.pop_back();
        assert!(next.is_some());

        if queue.is_empty() {
            self.has_entry &= !(1 << next_priority);
        }

        next
    }
}

impl Scheduler for PrioritizedLIFOScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let priority = {
            let mut node_inner = MCSNode::new();
            let info = task.info.lock(&mut node_inner);
            match info.scheduler_type {
                SchedulerType::PrioritizedLIFO(p) => p,
                _ => unreachable!(),
            }
        };

        let mut node = MCSNode::new();
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);
        if !self.invoke_preemption(task.clone()) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data.lock(&mut node_inner);
            let internal_data = data.get_or_insert_with(PrioritizedLIFOData::new);
            internal_data.push(
                priority,
                PrioritizedLIFOTask {
                    task: task.clone(),
                    _priority: priority,
                },
            );
        }
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        #[allow(clippy::question_mark)]
        let data = match data.as_mut() {
            Some(data) => data,
            None => return None,
        };

        loop {
            // Pop a task from the run queue.
            let task = data.pop()?;

            // Make the state of the task Running.
            {
                let mut node = MCSNode::new();
                let mut task_info = task.task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }

                if task_info.state == State::Preempted {
                    task_info.need_preemption = false;
                }
                if execution_ensured {
                    task_info.state = State::Running;
                    set_current_task(awkernel_lib::cpu::cpu_id(), task.task.id);
                }
            }

            return Some(task.task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::PrioritizedLIFO(0)
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

impl PrioritizedLIFOScheduler {
    fn invoke_preemption(&self, task: Arc<Task>) -> bool {
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

pub static SCHEDULER: PrioritizedLIFOScheduler = PrioritizedLIFOScheduler {
    data: Mutex::new(None),
    priority: get_priority(SchedulerType::PrioritizedLIFO(0)),
};