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
    cpu::{num_cpu, CpuSet},
    sync::mutex::{MCSNode, Mutex},
};

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

mod clustered_edf;
pub mod gedf;
pub(super) mod panicked;
mod prioritized_fifo;
mod prioritized_rr;

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

#[inline(always)]
pub fn move_preemption_pending(cpu_id: usize) -> Option<BinaryHeap<Arc<Task>>> {
    let mut node = MCSNode::new();
    let mut pending_tasks = PREEMPTION_PENDING_TASKS.lock(&mut node);
    pending_tasks.remove(&cpu_id)
}

/// Type of scheduler.
/// `u8` is the priority of priority based schedulers.
/// 0 is the lowest priority and 31 is the highest priority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchedulerType {
    /// Clustered EDF: `(relative_deadline, cpu_set)`.
    ///
    /// `cpu_set` is the set of cores the task may run on. It is normalized at
    /// spawn time: CPU 0 (the primary core) and any out-of-range bits are
    /// removed. If normalization leaves the set empty — e.g. an empty set, or
    /// one naming only CPU 0 or out-of-range cores — the task is **not**
    /// rejected; it falls back to all worker cores (`1..num_cpu()`) with a
    /// warning.
    ClusteredEDF(u64, CpuSet),
    GEDF(u64), // relative deadline
    PrioritizedFIFO(u8),
    PrioritizedRR(u8),
    Panicked,
}

impl SchedulerType {
    pub const fn equals(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (SchedulerType::GEDF(_), SchedulerType::GEDF(_))
                | (
                    SchedulerType::ClusteredEDF(_, _),
                    SchedulerType::ClusteredEDF(_, _)
                )
                | (
                    SchedulerType::PrioritizedFIFO(_),
                    SchedulerType::PrioritizedFIFO(_)
                )
                | (
                    SchedulerType::PrioritizedRR(_),
                    SchedulerType::PrioritizedRR(_)
                )
                | (SchedulerType::Panicked, SchedulerType::Panicked)
        )
    }

    /// Return the CPU affinity set if this is a [`SchedulerType::ClusteredEDF`] scheduler.
    ///
    /// Returns `Some(set)` where `set` is the set of CPU cores (`1..num_cpu()`) the task
    /// may run on. Returns `None` for all other scheduler variants.
    pub const fn cpu_set(&self) -> Option<CpuSet> {
        match self {
            SchedulerType::ClusteredEDF(_, set) => Some(*set),
            _ => None,
        }
    }

    /// True if this is a clustered scheduler, i.e. one whose tasks carry a
    /// CPU affinity set. Update this function when adding a new clustered
    /// scheduler; it is the single source of truth for the clustered prefix
    /// of `PRIORITY_LIST`.
    pub const fn is_clustered(&self) -> bool {
        matches!(self, SchedulerType::ClusteredEDF(_, _))
    }
}

/// # Priority
///
/// `priority()` returns the priority of the scheduler for preemption.
///
/// - The highest priority.
///   - Clustered EDF scheduler.
/// - The second highest priority.
///   - GEDF scheduler.
/// - The third highest priority.
///   - Prioritized FIFO scheduler.
/// - The fourth highest priority.
///   - Prioritized Round-Robin scheduler.
/// - The lowest priority.
///   - Panicked scheduler.
static PRIORITY_LIST: [SchedulerType; 5] = [
    SchedulerType::ClusteredEDF(0, CpuSet::empty()),
    SchedulerType::GEDF(0),
    SchedulerType::PrioritizedFIFO(0),
    SchedulerType::PrioritizedRR(0),
    SchedulerType::Panicked,
];

/// Return the number of clustered schedulers in `PRIORITY_LIST`.
const fn get_num_clustered_schedulers() -> usize {
    let mut count = 0;
    while count < PRIORITY_LIST.len() {
        if PRIORITY_LIST[count].is_clustered() {
            count += 1;
        } else {
            break;
        }
    }
    count
}

// `get_next_task` and `NUM_TASK_IN_QUEUE` accounting rely on the clustered
// schedulers forming a strict prefix of `PRIORITY_LIST`. Reject any reorder
// at compile time.
const _: () = {
    let mut i = get_num_clustered_schedulers();
    while i < PRIORITY_LIST.len() {
        assert!(
            !PRIORITY_LIST[i].is_clustered(),
            "clustered schedulers must form a strict prefix of PRIORITY_LIST"
        );
        i += 1;
    }
};

/// For exclusion execution of `wake_task` and `get_next` across all schedulers.
/// In order to resolve priority inversion in multiple priority-based schedulers,
/// the decision to preempt, dequeuing, enqueuing, and updating of RUNNING must be executed exclusively.
static GLOBAL_WAKE_GET_MUTEX: Mutex<()> = Mutex::new(());

/// # Implementing a clustered scheduler
///
/// A clustered scheduler keeps tasks that may run only on a subset of CPUs.
/// Every clustered scheduler must:
///
/// 1. Wrap each entry of its run queue in [`ClusteredTask`] so that
///    `NUM_CLUSTERED_TASKS_IN_QUEUE` is kept consistent.
/// 2. Implement [`Scheduler::queued_cpu_mask`] to report the exact set of
///    CPUs its queued tasks are runnable on (`wake_workers` relies on it).
/// 3. Be placed in the clustered prefix of `PRIORITY_LIST` and be matched by
///    `SchedulerType::is_clustered` (checked at compile time).
pub(crate) trait Scheduler {
    /// Enqueue an executable task.
    /// The enqueued task will be taken by `get_next()`.
    fn wake_task(&self, task: Arc<Task>);

    /// Get the next executable task.
    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>>;

    /// Get the scheduler name.
    fn scheduler_name(&self) -> SchedulerType;

    #[allow(dead_code)] // TODO: to be removed
    fn priority(&self) -> u8;

    /// The set of CPUs that have at least one queued task eligible to run on
    /// them. Non-clustered schedulers use the default (empty) implementation;
    /// clustered schedulers must override it.
    fn queued_cpu_mask(&self) -> CpuSet {
        CpuSet::empty()
    }
}

/// Return the union of [`Scheduler::queued_cpu_mask`] over all clustered
/// schedulers: the exact set of CPUs for which a clustered task is queued.
pub(crate) fn clustered_queued_cpu_mask() -> CpuSet {
    let mut mask = CpuSet::empty();
    for scheduler_type in &PRIORITY_LIST[..get_num_clustered_schedulers()] {
        mask = mask.union(get_scheduler(scheduler_type).queued_cpu_mask());
    }
    mask
}

/// Get the next executable task.
#[inline]
pub(crate) fn get_next_task(execution_ensured: bool) -> Option<Arc<Task>> {
    let mut node = MCSNode::new();
    let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);

    let num_clustered_tasks = crate::task::NUM_CLUSTERED_TASKS_IN_QUEUE.load(Ordering::Relaxed);

    // The counter is global: it may be non-zero even when no queued clustered
    // task is runnable on this CPU. That is fine because the run queues fail
    // fast (`pop_for_cpu` checks the root affinity mask in O(1)).
    if num_clustered_tasks > 0 {
        let task = PRIORITY_LIST[..get_num_clustered_schedulers()]
            .iter()
            .find_map(|scheduler_type| get_scheduler(scheduler_type).get_next(execution_ensured));

        // The counter is decremented by the ClusteredTask::take() call inside
        // get_next() (Drop is a no-op once take() has run).
        if task.is_some() {
            return task;
        }
    }

    // Skip the clustered prefix: it was either just tried above and returned
    // None (the queue state cannot change in between because both `wake_task`
    // and `get_next_task` hold `GLOBAL_WAKE_GET_MUTEX`), or the counter was 0
    // and its queues are empty. This also structurally guarantees that the
    // `NUM_TASK_IN_QUEUE` decrement below never applies to a clustered task,
    // which is counted by `NUM_CLUSTERED_TASKS_IN_QUEUE` instead.
    let task = PRIORITY_LIST[get_num_clustered_schedulers()..]
        .iter()
        .find_map(|scheduler_type| get_scheduler(scheduler_type).get_next(execution_ensured));

    if task.is_some() {
        crate::task::NUM_TASK_IN_QUEUE.fetch_sub(1, Ordering::Relaxed);
    }

    task
}

/// Get a scheduler.
///
/// Takes `&SchedulerType` so the caller does not copy the full payload (the
/// embedded `CpuSet` makes `SchedulerType` large); only the discriminant is
/// matched.
pub(crate) fn get_scheduler(sched_type: &SchedulerType) -> &'static dyn Scheduler {
    match sched_type {
        SchedulerType::PrioritizedFIFO(_) => &prioritized_fifo::SCHEDULER,
        SchedulerType::PrioritizedRR(_) => &prioritized_rr::SCHEDULER,
        SchedulerType::GEDF(_) => &gedf::SCHEDULER,
        SchedulerType::ClusteredEDF(_, _) => &clustered_edf::SCHEDULER,
        SchedulerType::Panicked => &panicked::SCHEDULER,
    }
}

pub const fn get_priority(sched_type: &SchedulerType) -> u8 {
    let mut index = 0;
    while index < PRIORITY_LIST.len() {
        if PRIORITY_LIST[index].equals(sched_type) {
            return (PRIORITY_LIST.len() - 1 - index) as u8;
        }
        index += 1;
    }
    panic!("Scheduler type not registered in PRIORITY_LIST or equals()")
}

/// RAII wrapper representing one slot in `NUM_CLUSTERED_TASKS_IN_QUEUE`.
///
/// Constructing a `ClusteredTask` increments the counter. The counter is
/// decremented exactly once — either via [`take`] (explicit ownership
/// transfer) or via `Drop` (e.g. when a terminated task is discarded). If
/// `take` has already been called, `Drop` is a no-op.
///
/// [`take`]: ClusteredTask::take
pub(crate) struct ClusteredTask<T> {
    inner: Option<T>,
}

impl<T> ClusteredTask<T> {
    pub(crate) fn new(inner: T) -> Self {
        crate::task::NUM_CLUSTERED_TASKS_IN_QUEUE.fetch_add(1, Ordering::Relaxed);
        Self { inner: Some(inner) }
    }

    /// Take the inner value and decrement the counter.
    ///
    /// Returns `None` if the value has already been taken.
    /// After this call `Drop` will be a no-op.
    pub(crate) fn take(&mut self) -> Option<T> {
        let val = self.inner.take();
        if val.is_some() {
            crate::task::NUM_CLUSTERED_TASKS_IN_QUEUE.fetch_sub(1, Ordering::Relaxed);
        }
        val
    }
}

impl<T> Drop for ClusteredTask<T> {
    fn drop(&mut self) {
        // Decrement only if take() has not been called yet.
        if self.inner.is_some() {
            crate::task::NUM_CLUSTERED_TASKS_IN_QUEUE.fetch_sub(1, Ordering::Relaxed);
        }
    }
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
            if let Some(SchedulerType::PrioritizedRR(_)) = get_scheduler_type_by_task_id(task_id) {
                prioritized_rr::SCHEDULER.invoke_preemption_tick(cpu_id, task_id)
            }
        }
    }

    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.wake_task();
    guard.time_to_wait()
}
