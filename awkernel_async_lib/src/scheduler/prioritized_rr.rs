//! A Priority Based RR scheduler

use core::cmp::max;

use super::{take_head_if, ConditionalNext, Scheduler, SchedulerType, Task};
use crate::{
    scheduler::{
        get_next_task_if, get_priority, peek_preemption_pending, push_preemption_pending,
        GLOBAL_WAKE_GET_MUTEX, PREEMPTION_ENABLED,
    },
    task::{
        get_task, get_tasks_running, set_current_task, set_need_preemption, State,
        NUM_TASK_IN_QUEUE,
    },
};
use alloc::{sync::Arc, vec::Vec};
use awkernel_lib::priority_queue::PriorityQueue;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::sync::atomic::Ordering;
use core::time::Duration;

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
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);
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
            NUM_TASK_IN_QUEUE.fetch_add(1, Ordering::Relaxed);
            drop(data);

            // Every enqueue goes through this function, including the re-wakes
            // that bypass `ArcWake::wake`, so notify the primary CPU here to
            // wake an idle worker.
            awkernel_lib::cpu::wake_cpu(0);
        }
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut guard = self.data.lock(&mut node);

        #[allow(clippy::question_mark)]
        let data = match guard.as_mut() {
            Some(data) => data,
            None => return None,
        };

        while let Some(rr_task) = data.queue.pop() {
            NUM_TASK_IN_QUEUE.fetch_sub(1, Ordering::Relaxed);
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

    fn get_next_if(&self, pred: &dyn Fn(&Task) -> bool) -> ConditionalNext {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        match (*data).as_mut() {
            Some(data) => take_head_if(&mut data.queue, |entry| &entry.task, pred),
            None => ConditionalNext::Empty,
        }
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
    priority: get_priority(&SchedulerType::PrioritizedRR(0)),
};

impl PrioritizedRRScheduler {
    /// Rotate the PrioritizedRR task `task_id` running on `cpu_id` if it has
    /// used up its time quantum.
    ///
    /// The next runnable task is dequeued and sent to `cpu_id` only if its
    /// priority is at least that of the running task: an equal priority is
    /// the quantum rotation, and a higher priority is a plain preemption.
    /// A lower-priority task could not preempt the running task anyway, so
    /// it is left in the run queue to keep its position, and the quantum of
    /// the running task is restarted instead.
    ///
    /// Returns the time after which this function must be called again for
    /// this CPU, or `None` if a preemption was requested: the preempted task
    /// is enqueued again, and that wakes the primary CPU.
    ///
    /// This function must be called on the primary CPU.
    pub fn invoke_preemption_tick(&self, cpu_id: usize, task_id: u32) -> Option<Duration> {
        let current_task = get_task(task_id)?;
        let interval = Duration::from_micros(self.interval);

        let elapsed = {
            let mut node = MCSNode::new();
            let info = current_task.info.lock(&mut node);
            info.get_last_executed().elapsed()
        };

        if elapsed <= interval {
            return Some(interval - elapsed);
        }

        // A task is dequeued only while no preemption is pending on this
        // CPU: `do_preemption` runs one pending task and re-queues the others
        // at the tail of their level. The predicate runs under
        // `GLOBAL_WAKE_GET_MUTEX`, so no wake path can push a pending task
        // between this check and the dequeue.
        let next_task = get_next_task_if(|next| {
            peek_preemption_pending(cpu_id).is_none() && !current_task.preempts(next)
        });

        if let Some(next_task) = next_task {
            push_preemption_pending(cpu_id, next_task);
            let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
            set_need_preemption(task_id, cpu_id);
            awkernel_lib::interrupt::send_ipi(preempt_irq, cpu_id as u32);
            return None;
        }

        if peek_preemption_pending(cpu_id).is_some() {
            // A preemption has already been requested on this CPU, but it
            // has not been performed yet. Request it again in case the IPI
            // was not handled.
            let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
            set_need_preemption(task_id, cpu_id);
            awkernel_lib::interrupt::send_ipi(preempt_irq, cpu_id as u32);
        } else {
            // There is no task to rotate with. Restart the quantum so that
            // the run queues are not examined again on every tick.
            let mut node = MCSNode::new();
            let mut info = current_task.info.lock(&mut node);
            info.update_last_executed();
        }

        Some(interval)
    }

    fn invoke_preemption_wake(&self, task: Arc<Task>) -> bool {
        if !PREEMPTION_ENABLED {
            return false;
        }

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
        if task.preempts(&target_task) {
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
