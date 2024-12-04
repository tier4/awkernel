//! Define types and trait for the Autoware Kernel scheduler.
//! This module contains `SleepingTasks` for sleeping.

use crate::task::{
    get_current_task, get_last_executed_by_task_id, get_scheduler_type_by_task_id,
    get_tasks_running, set_need_preemption,
};
use crate::{delay::uptime, task::Task};
use alloc::sync::Arc;
use awkernel_async_lib_verified::delta_list::DeltaList;
use awkernel_lib::{
    cpu::num_cpu,
    sync::mutex::{MCSNode, Mutex},
};

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

mod fifo;
pub mod gedf;
pub(super) mod panicked;
mod prioritized_fifo;
mod priority_based_rr;
mod rr;

static SLEEPING: Mutex<SleepingTasks> = Mutex::new(SleepingTasks::new());

/// Type of scheduler.
/// `u8` is the priority of priority based schedulers.
/// 0 is the highest priority and 99 is the lowest priority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchedulerType {
    FIFO,

    PrioritizedFIFO(u8),

    RR,

    PriorityBasedRR(u8),

    GEDF(u64), //relative deadline

    Panicked,
}

/// # Priority
///
/// `priority()` returns the priority of the scheduler for preemption.
///
/// - The highest priority.
///   - GEDF scheduler.
/// - The second highest priority.
///   - FIFO scheduler.
///   - Prioritized FIFO scheduler.
/// - The third highest priority.
///   - Round-Robin scheduler.
///   - Priority-based Round-Robin scheduler.
/// - The lowest priority.
///   - Panicked scheduler.
static PRIORITY_LIST: [SchedulerType; 6] = [
    SchedulerType::GEDF(0),
    SchedulerType::FIFO,
    SchedulerType::PrioritizedFIFO(0),
    SchedulerType::RR,
    SchedulerType::PriorityBasedRR(0),
    SchedulerType::Panicked,
];

pub(crate) trait Scheduler {
    /// Enqueue an executable task.
    /// The enqueued task will be taken by `get_next()`.
    fn wake_task(&self, task: Arc<Task>);

    /// Get the next executable task.
    fn get_next(&self) -> Option<Arc<Task>>;

    /// Get the scheduler name.
    fn scheduler_name(&self) -> SchedulerType;

    /// Get the priority of the scheduler.
    fn priority(&self) -> u8 {
        PRIORITY_LIST
            .iter()
            .position(|&x| x == self.scheduler_name())
            .unwrap_or(PRIORITY_LIST.len()) as u8
    }

    /// Invoke preemption.
    fn scheduler_preemption(&self) -> bool {
        // Get running tasks and filter out tasks with task_id == 0.
        let mut tasks = get_tasks_running();
        tasks.retain(|task| task.task_id != 0);

        // If the number of running tasks is less than the number of non-primary CPUs, preempt is not required.
        let num_non_primary_cpus = num_cpu().saturating_sub(1);
        if tasks.len() < num_non_primary_cpus {
            return false;
        }

        let mut lowest_task_info: Option<(u8, usize, u32)> = None; // (priority, cpu_id, task_id)

        // Find the lowest priority task.
        for task in tasks {
            if let Some(task_sched_type) = get_scheduler_type_by_task_id(task.task_id) {
                let task_priority = get_scheduler(task_sched_type).priority();
                match lowest_task_info {
                    // If the priority of the scheduler is lower than the lowest priority task.
                    Some((lowest_priority, _, _)) if task_priority > lowest_priority => {
                        lowest_task_info = Some((task_priority, task.cpu_id, task.task_id));
                    }
                    // If the priority of the scheduler is the same as the lowest priority task.
                    Some((lowest_priority, _, task_id)) if task_priority == lowest_priority => {
                        if get_last_executed_by_task_id(task.task_id)
                            < get_last_executed_by_task_id(task_id)
                        {
                            lowest_task_info = Some((task_priority, task.cpu_id, task.task_id));
                        }
                    }
                    // If the priority of the scheduler is higher than the lowest priority task.
                    Some((lowest_priority, _, _)) if task_priority < lowest_priority => {
                        // Do nothing.
                    }
                    // The first task.
                    _ => {
                        lowest_task_info = Some((task_priority, task.cpu_id, task.task_id));
                    }
                }
            }
        }

        // Preempt the task if the priority of the scheduler is higher than the lowest priority task.
        if let Some((lowest_priority, cpu_id, task_id)) = lowest_task_info {
            if lowest_priority > self.priority() {
                let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
                set_need_preemption(task_id);
                awkernel_lib::interrupt::send_ipi(preempt_irq, cpu_id as u32);
                return true;
            }
        }
        false
    }
}

/// Get the next executable task.
#[inline]
pub(crate) fn get_next_task() -> Option<Arc<Task>> {
    PRIORITY_LIST
        .iter()
        .find_map(|&scheduler_type| get_scheduler(scheduler_type).get_next())
}

/// Get a scheduler.
pub(crate) fn get_scheduler(sched_type: SchedulerType) -> &'static dyn Scheduler {
    match sched_type {
        SchedulerType::FIFO => &fifo::SCHEDULER,
        SchedulerType::PrioritizedFIFO(_) => &prioritized_fifo::SCHEDULER,
        SchedulerType::RR => &rr::SCHEDULER,
        SchedulerType::PriorityBasedRR(_) => &priority_based_rr::SCHEDULER,
        SchedulerType::GEDF(_) => &gedf::SCHEDULER,
        SchedulerType::Panicked => &panicked::SCHEDULER,
    }
}

/// Maintain sleeping tasks by a delta list.
struct SleepingTasks {
    delta_list: DeltaList<Box<dyn FnOnce() + Send>>,
    base_time: u64,
}

impl SleepingTasks {
    const fn new() -> Self {
        Self {
            delta_list: DeltaList::Nil,
            base_time: 0,
        }
    }

    /// `dur` is microseconds
    fn sleep_task(&mut self, handler: Box<dyn FnOnce() + Send>, mut dur: u64) {
        let now = uptime();
        if self.delta_list.is_empty() {
            self.base_time = now;
        } else {
            let diff = now - self.base_time;
            dur += diff;
        }

        self.delta_list.insert(dur, handler);
    }

    /// Wake tasks up.
    fn wake_task(&mut self) {
        let now = uptime();

        while let Some((dur, _)) = self.delta_list.front() {
            let elapsed = now - self.base_time;
            if dur <= elapsed {
                // Timed out.
                if let DeltaList::Cons(data) = self.delta_list.pop().unwrap() {
                    let (_, handler, _) = data.into_inner();
                    handler(); // Invoke a handler.

                    self.base_time += dur;
                }
            } else {
                break;
            }
        }
    }
}

/// After `dur` time, `sleep_handler` will be invoked.
/// `dur` is microseconds.
pub(crate) fn sleep_task(sleep_handler: Box<dyn FnOnce() + Send>, dur: u64) {
    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.sleep_task(sleep_handler, dur);
}

/// Wake executable tasks up.
/// Waked tasks will be enqueued to their scheduler's queue.
///
/// This function should be called from only Autoware Kernel.
/// So, do not call this from userland.
pub fn wake_task() {
    // Check whether each running task exceeds the time quantum.
    for cpu_id in 1..num_cpu() {
        if let Some(task_id) = get_current_task(cpu_id) {
            match get_scheduler_type_by_task_id(task_id) {
                Some(SchedulerType::RR) => rr::SCHEDULER.invoke_preemption(cpu_id, task_id),
                Some(SchedulerType::PriorityBasedRR(_)) => {
                    priority_based_rr::SCHEDULER.invoke_preemption(cpu_id, task_id)
                }
                _ => (),
            }
        }
    }

    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.wake_task();
}
