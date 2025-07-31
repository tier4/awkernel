//! A prioritized FIFO scheduler.

use core::cmp::max;

use super::{Scheduler, SchedulerType, Task};
use crate::scheduler::{peek_preemption_pending, push_preemption_pending};
use crate::task::{get_task, get_tasks_running, set_current_task, set_need_preemption};
use crate::{scheduler::get_priority, task::State};
use alloc::sync::Arc;
use alloc::vec::Vec;
use awkernel_lib::priority_queue::PriorityQueue;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct PrioritizedFIFOScheduler {
    data: Mutex<Option<PrioritizedFIFOData>>, // Run queue.
    priority: u8,
}

struct PrioritizedFIFOTask {
    task: Arc<Task>,
    _priority: u8,
}

struct PrioritizedFIFOData {
    queue: PriorityQueue<PrioritizedFIFOTask>,
}

impl PrioritizedFIFOData {
    fn new() -> Self {
        Self {
            queue: PriorityQueue::new(),
        }
    }
}

impl Scheduler for PrioritizedFIFOScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        // The reason for acquiring this lock before invoke_preemption() is to prevent priority inversion from occurring
        // when invoke_preemption() is executed between the time the next task is determined and the RUNNING is updated
        // within the scheduler's get_next().
        let mut data = self.data.lock(&mut node);
        let internal_data = data.get_or_insert_with(PrioritizedFIFOData::new);
        let priority = {
            let mut node_inner = MCSNode::new();
            let info = task.info.lock(&mut node_inner);
            match info.scheduler_type {
                SchedulerType::PrioritizedFIFO(p) => p,
                _ => unreachable!(),
            }
        };

        if !self.invoke_preemption(task.clone()) {
            internal_data.queue.push(
                priority,
                PrioritizedFIFOTask {
                    task: task.clone(),
                    _priority: priority,
                },
            );
        }
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        #[allow(clippy::question_mark)]
        let data = match data.as_mut() {
            Some(data) => data,
            None => return None,
        };

        loop {
            // Pop a task from the run queue.
            let task = data.queue.pop()?;

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
                task_info.state = State::Running;
                set_current_task(awkernel_lib::cpu::cpu_id(), task.task.id);
            }

            return Some(task.task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::PrioritizedFIFO(0)
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

impl PrioritizedFIFOScheduler {
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

            return true;
        }

        false
    }
}

pub static SCHEDULER: PrioritizedFIFOScheduler = PrioritizedFIFOScheduler {
    data: Mutex::new(None),
    priority: get_priority(SchedulerType::PrioritizedFIFO(0)),
};
