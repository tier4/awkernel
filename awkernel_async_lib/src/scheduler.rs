//! Define types and trait for the Autoware Kernel scheduler.
//! This module contains `SleepingTasks` for sleeping.

use crate::{delay::uptime, task::Task};
use alloc::{boxed::Box, sync::Arc};
use awkernel_async_lib_verified::delta_list::DeltaList;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

mod prioritized_round_robin;
mod round_robin;

static SLEEPING: Mutex<SleepingTasks> = Mutex::new(SleepingTasks::new());

/// Type of scheduler.
#[derive(Debug, Clone, Copy)]
pub enum SchedulerType {
    RoundRobin,
    PrioritizedRoundRobin(u8),
}

pub(crate) trait Scheduler {
    /// Enqueue an executable task.
    /// The enqueued task will be taken by `get_next()`.
    fn wake_task(&self, task: Arc<Task>);

    /// Get the next executable task.
    fn get_next(&self) -> Option<Arc<Task>>;

    /// Get the scheduler name.
    fn scheduler_name(&self) -> SchedulerType;
}

/// Get the next executable task.
pub(crate) fn get_next_task() -> Option<Arc<Task>> {
    if let Some(task) = round_robin::SCHEDULER.get_next() {
        return Some(task);
    }

    if let Some(task) = prioritized_round_robin::SCHEDULER.get_next() {
        return Some(task);
    }

    None
}

/// Get a scheduler.
pub(crate) fn get_scheduler(sched_type: SchedulerType) -> &'static dyn Scheduler {
    match sched_type {
        SchedulerType::RoundRobin => &round_robin::SCHEDULER,
        SchedulerType::PrioritizedRoundRobin(priority) => &prioritized_round_robin::SCHEDULER,
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
    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.wake_task();
}
