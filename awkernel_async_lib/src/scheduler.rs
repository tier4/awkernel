//! Define types and trait for the Autoware Kernel scheduler.
//! This module contains `SleepingTasks` for sleeping.

use crate::task::{get_current_task, get_scheduler_type_by_task_id};
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
/// 0 is the highest priority and 255 is the lowest priority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchedulerType {
    FIFO,

    PrioritizedFIFO(u8),

    RR,

    PriorityBasedRR(u8),

    GEDF(u64, u64, u64), // period, relative deadline, spawn time

    Panicked,
}

/// # Priority
///
/// `priority()` returns the priority of the scheduler for preemption.
///
/// - 0: The highest priority.
///   - FIFO scheduler.
///   - Prioritized FIFO scheduler.
///   - Tasks using these schedulers will not be preempted.
/// - 1 - 16
///   - Round-Robin scheduler.
/// - 255: The lowest priority.
///   - Panicked scheduler.
pub(crate) trait Scheduler {
    /// Enqueue an executable task.
    /// The enqueued task will be taken by `get_next()`.
    fn wake_task(&self, task: Arc<Task>);

    /// Get the next executable task.
    fn get_next(&self) -> Option<Arc<Task>>;

    /// Get the scheduler name.
    fn scheduler_name(&self) -> SchedulerType;

    #[allow(dead_code)] // TODO: to be removed
    fn priority(&self) -> u8;
}

/// Get the next executable task.
pub(crate) fn get_next_task() -> Option<Arc<Task>> {
    if let Some(task) = fifo::SCHEDULER.get_next() {
        return Some(task);
    }

    if let Some(task) = prioritized_fifo::SCHEDULER.get_next() {
        return Some(task);
    }

    if let Some(task) = rr::SCHEDULER.get_next() {
        return Some(task);
    }

    if let Some(task) = priority_based_rr::SCHEDULER.get_next() {
        return Some(task);
    }

    if let Some(task) = gedf::SCHEDULER.get_next() {
        return Some(task);
    }

    if let Some(task) = panicked::SCHEDULER.get_next() {
        return Some(task);
    }

    None
}

/// Get a scheduler.
pub(crate) fn get_scheduler(sched_type: SchedulerType) -> &'static dyn Scheduler {
    match sched_type {
        SchedulerType::FIFO => &fifo::SCHEDULER,
        SchedulerType::PrioritizedFIFO(_) => &prioritized_fifo::SCHEDULER,
        SchedulerType::RR => &rr::SCHEDULER,
        SchedulerType::PriorityBasedRR(_) => &priority_based_rr::SCHEDULER,
        SchedulerType::GEDF(_, _, _) => &gedf::SCHEDULER,
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
