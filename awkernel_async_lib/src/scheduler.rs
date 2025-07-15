//! Define types and trait for the Awkernel scheduler.
//! This module contains `SleepingTasks` for sleeping.

use core::sync::atomic::Ordering;
use core::time::Duration;

use crate::task::Task;
use crate::task::{get_current_task, get_scheduler_type_by_task_id};
use alloc::collections::{binary_heap::BinaryHeap, btree_map::BTreeMap};
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

static SLEEPING: Mutex<SleepingTasks> = Mutex::new(SleepingTasks::new());

/// Tasks that request preemption by IPI. The key is the IPI destination CPU ID.
static PREEMPTION_PENDING_TASKS: Mutex<BTreeMap<usize, BinaryHeap<Arc<Task>>>> =
    Mutex::new(BTreeMap::new());

#[inline(always)]
pub fn peek_preemption_pending(cpu_id: usize) -> Option<Arc<Task>> {
    let mut node = MCSNode::new();
    let pending_tasks = PREEMPTION_PENDING_TASKS.lock(&mut node);
    pending_tasks
        .get(&cpu_id)
        .and_then(|heap| heap.peek().cloned())
}

#[inline(always)]
pub fn remove_preemption_pending(cpu_id: usize, task_id: u32) {
    let mut node = MCSNode::new();
    let mut pending_tasks = PREEMPTION_PENDING_TASKS.lock(&mut node);
    if let Some(heap) = pending_tasks.get_mut(&cpu_id) {
        heap.retain(|task| task.id != task_id);
    }
}

#[inline(always)]
pub fn push_preemption_pending(cpu_id: usize, task: Arc<Task>) {
    let mut node = MCSNode::new();
    let mut pending_tasks = PREEMPTION_PENDING_TASKS.lock(&mut node);
    pending_tasks.entry(cpu_id).or_default().push(task);
}

#[inline(always)]
pub fn pop_preemption_pending(cpu_id: usize) -> Option<Arc<Task>> {
    let mut node = MCSNode::new();
    let mut pending_tasks = PREEMPTION_PENDING_TASKS.lock(&mut node);
    pending_tasks.get_mut(&cpu_id).and_then(|heap| heap.pop())
}

/// Type of scheduler.
/// `u8` is the priority of priority based schedulers.
/// 0 is the highest priority and 99 is the lowest priority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchedulerType {
    GEDF(u64), // relative deadline
    FIFO,
    PrioritizedFIFO(u8),
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
static PRIORITY_LIST: [SchedulerType; 5] = [
    SchedulerType::GEDF(0),
    SchedulerType::PrioritizedFIFO(0),
    SchedulerType::FIFO,
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

    #[allow(dead_code)] // TODO: to be removed
    fn priority(&self) -> u8;
}

/// Get the next executable task.
#[inline]
pub(crate) fn get_next_task() -> Option<Arc<Task>> {
    let task = PRIORITY_LIST
        .iter()
        .find_map(|&scheduler_type| get_scheduler(scheduler_type).get_next());

    if task.is_some() {
        crate::task::NUM_TASK_IN_QUEUE.fetch_sub(1, Ordering::Relaxed);
    }

    task
}

/// Get a scheduler.
pub(crate) fn get_scheduler(sched_type: SchedulerType) -> &'static dyn Scheduler {
    match sched_type {
        SchedulerType::FIFO => &fifo::SCHEDULER,
        SchedulerType::PrioritizedFIFO(_) => &prioritized_fifo::SCHEDULER,
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
    base_time: awkernel_lib::time::Time,
}

impl SleepingTasks {
    const fn new() -> Self {
        Self {
            delta_list: DeltaList::Nil,
            base_time: awkernel_lib::time::Time::zero(),
        }
    }

    /// `dur` is a Duration.
    fn sleep_task(&mut self, handler: Box<dyn FnOnce() + Send>, mut dur: Duration) {
        if self.delta_list.is_empty() {
            self.base_time = awkernel_lib::time::Time::now();
        } else {
            let diff = self.base_time.elapsed();
            dur += diff;
        }

        self.delta_list.insert(dur.as_nanos() as u64, handler);
    }

    /// Wake tasks up.
    fn wake_task(&mut self) {
        while let Some((dur, _)) = self.delta_list.front() {
            let dur = Duration::from_nanos(dur);
            let elapsed = self.base_time.elapsed();

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

    /// Get the duration of between the current time and the time of the head.
    fn time_to_wait(&self) -> Option<Duration> {
        let (dur, _) = self.delta_list.front()?;
        let elapsed = self.base_time.elapsed().as_nanos() as u64;

        if elapsed >= dur {
            Some(Duration::from_nanos(0))
        } else {
            Some(Duration::from_nanos(dur - elapsed))
        }
    }
}

/// After `dur` time, `sleep_handler` will be invoked.
/// `dur` is microseconds.
pub(crate) fn sleep_task(sleep_handler: Box<dyn FnOnce() + Send>, dur: Duration) {
    {
        let mut node = MCSNode::new();
        let mut guard = SLEEPING.lock(&mut node);
        guard.sleep_task(sleep_handler, dur);
    }

    awkernel_lib::cpu::wake_cpu(0);
}

/// Wake executable tasks up.
/// Waked tasks will be enqueued to their scheduler's queue.
///
/// This function should be called from only Awkernel.
/// So, do not call this from userland.
///
/// # Return Value
///
/// If there are sleeping tasks, this function returns the duration to wait.
/// If there are no sleeping tasks, this function returns `None`.
pub fn wake_task() -> Option<Duration> {
    // Check whether each running task exceeds the time quantum.
    for cpu_id in 1..num_cpu() {
        if let Some(task_id) = get_current_task(cpu_id) {
            if let Some(SchedulerType::PriorityBasedRR(_)) = get_scheduler_type_by_task_id(task_id)
            {
                priority_based_rr::SCHEDULER.invoke_preemption(cpu_id, task_id)
            }
        }
    }

    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.wake_task();
    guard.time_to_wait()
}
