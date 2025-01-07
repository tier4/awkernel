//! Define types and trait for the Autoware Kernel scheduler.
//! This module contains `SleepingTasks` for sleeping.

use crate::task::{
    get_current_task, get_lowest_priority_task_info, get_scheduler_type_by_task_id,
    set_need_preemption, PriorityInfo,
};
use crate::{delay::uptime, task::Task};
use alloc::sync::Arc;
use awkernel_async_lib_verified::delta_list::DeltaList;
use awkernel_lib::{
    cpu::num_cpu,
    sync::mutex::{MCSNode, Mutex},
};
use core::{
    sync::atomic::{AtomicUsize, Ordering},
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
static NUM_SEND_IPI: AtomicUsize = AtomicUsize::new(0); // The number of send IPI.

/// Type of scheduler.
/// `u8` is the priority of priority based schedulers.
/// 0 is the highest priority and 99 is the lowest priority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchedulerType {
    GEDF(u64), // relative deadline
    FIFO,
    PrioritizedFIFO(u8),
    RR,
    PriorityBasedRR(u8),
    Panicked,
}

impl SchedulerType {
    pub const fn equals(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (SchedulerType::GEDF(_), SchedulerType::GEDF(_))
                | (SchedulerType::FIFO, SchedulerType::FIFO)
                | (
                    SchedulerType::PrioritizedFIFO(_),
                    SchedulerType::PrioritizedFIFO(_)
                )
                | (SchedulerType::RR, SchedulerType::RR)
                | (
                    SchedulerType::PriorityBasedRR(_),
                    SchedulerType::PriorityBasedRR(_)
                )
                | (SchedulerType::Panicked, SchedulerType::Panicked)
        )
    }
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
    SchedulerType::PrioritizedFIFO(0),
    SchedulerType::FIFO,
    SchedulerType::PriorityBasedRR(0),
    SchedulerType::RR,
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
    fn priority(&self) -> u8;

    /// Invoke preemption.
    fn invoke_preemption(&self, wake_task_priority: PriorityInfo) {
        let mut last_preempt_task_id = None;

        while let Some((task_id, cpu_id, lowest_priority_info)) = get_lowest_priority_task_info() {
            if Some(task_id) == last_preempt_task_id {
                continue;
            }

            if wake_task_priority < lowest_priority_info {
                if NUM_SEND_IPI.load(Ordering::Relaxed) != 0 {
                    last_preempt_task_id = Some(task_id);
                    continue;
                }

                let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
                NUM_SEND_IPI.fetch_add(1, Ordering::Relaxed);
                set_need_preemption(task_id);
                awkernel_lib::interrupt::send_ipi(preempt_irq, cpu_id as u32);
                NUM_SEND_IPI.fetch_sub(1, Ordering::Relaxed);
            }
            return;
        }
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

pub const fn get_priority(sched_type: SchedulerType) -> u8 {
    let mut priority = 0;
    while priority < PRIORITY_LIST.len() {
        if PRIORITY_LIST[priority].equals(&sched_type) {
            return priority as u8;
        }
        priority += 1;
    }
    panic!("Scheduler type not registered in PRIORITY_LIST or equals()")
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
                Some(SchedulerType::RR) => rr::SCHEDULER.invoke_rr_preemption(cpu_id, task_id),
                Some(SchedulerType::PriorityBasedRR(_)) => {
                    priority_based_rr::SCHEDULER.invoke_rr_preemption(cpu_id, task_id)
                }
                _ => (),
            }
        }
    }

    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.wake_task();
}
