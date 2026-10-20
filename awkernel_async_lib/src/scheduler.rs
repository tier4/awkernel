//! Define types and trait for the Awkernel scheduler.
//! This module contains `SleepingTasks` for sleeping.

use core::sync::atomic::Ordering;
use core::time::Duration;

use crate::{
    task::{get_current_task, get_scheduler_type_by_task_id, Task},
    time::Instant,
};
use alloc::collections::{binary_heap::BinaryHeap, btree_map::BTreeMap};
use alloc::sync::Arc;
use awkernel_async_lib_verified::delta_list::DeltaList;
use awkernel_lib::{
    cpu::{num_cpu, CpuSet},
    sync::mutex::{MCSNode, Mutex},
};

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

pub(crate) mod active_vp;
mod clustered_edf;
pub mod dp_wrap;
pub mod gedf;
pub(crate) mod mixed_vp;
pub(super) mod panicked;
pub(crate) mod passive_vp;
pub(crate) mod pool;
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
    /// V-Fed active-VP scheduling: `(cpu_set, leading_cpu)` (see
    /// `dag_sched::policy::vfed` and `scheduler::active_vp`). `cpu_set` is
    /// a heavy DAG's dedicated active-VP group, normalized the same way as
    /// `ClusteredEDF`'s; `leading_cpu` (a member of `cpu_set`) is the one
    /// core privileged to be tried first for any eligible vertex. Each
    /// core's replenishable per-job execution budget is tracked separately
    /// (`active_vp::set_initial_budget`), not carried here.
    ActiveVp(CpuSet, usize),
    /// V-Fed mixed active+passive scheduling (Theorem 4):
    /// `(active_set, leading_cpu, passive_set)` — a heavy DAG's own
    /// (possibly partial) active-VP group plus other DAGs' leftover
    /// passive-VPs pulled in to top it up (see `dag_sched::policy::vfed`'s
    /// `VFedAssignment::Heavy` with a non-empty `passive`, and
    /// `scheduler::mixed_vp`). `active_set`/`leading_cpu` are normalized and
    /// budget/leading-gated exactly like `ActiveVp`'s; `passive_set` is
    /// normalized and gated exactly like `PassiveVp`'s. Disjoint from
    /// `active_set` by construction (a DAG never borrows its own cores).
    MixedVp(CpuSet, usize, CpuSet),
    /// Clustered EDF: `(relative_deadline, cpu_set)`.
    ///
    /// `cpu_set` is the set of cores the task may run on. It is normalized at
    /// spawn time: CPU 0 (the primary core) and any out-of-range bits are
    /// removed. If normalization leaves the set empty — e.g. an empty set, or
    /// one naming only CPU 0 or out-of-range cores — the task is **not**
    /// rejected; it falls back to all worker cores (`1..num_cpu()`) with a
    /// warning.
    ClusteredEDF(u64, CpuSet),
    /// V-Fed passive-VP scheduling: `cpu_set` (see
    /// `dag_sched::policy::vfed` and `scheduler::passive_vp`) — the set of
    /// other DAGs' leftover active-VP cores this task draws on. Normalized
    /// the same way as `ClusteredEDF`'s. No leading/budget concept: dispatch
    /// is gated purely by whether each core's active-VP owner is currently
    /// executing there (`passive_vp::active_vp_is_busy`).
    PassiveVp(CpuSet),
    GEDF(u64), // relative deadline
    /// DAG-Fluid's real dispatch (`dag_sched::dp_partition` /
    /// `scheduler::dp_wrap`): `dag_id`, the DAG this node belongs to. Unlike
    /// `ClusteredEDF`/`ActiveVp`, the CPU set a `DpWrap` task may run on is
    /// **not** carried here — it is looked up dynamically at dispatch time
    /// from `scheduler::dp_wrap`'s own per-CPU entitlement table, which
    /// changes over time as Deadline Partitions advance (see that module's
    /// own doc). `cpu_set()`/`is_clustered()` therefore both treat this
    /// variant like any non-clustered scheduler.
    DpWrap(u32),
    PrioritizedFIFO(u8),
    PrioritizedRR(u8),
    Panicked,
}

impl SchedulerType {
    pub const fn equals(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (SchedulerType::ActiveVp(_, _), SchedulerType::ActiveVp(_, _))
                | (
                    SchedulerType::MixedVp(_, _, _),
                    SchedulerType::MixedVp(_, _, _)
                )
                | (SchedulerType::GEDF(_), SchedulerType::GEDF(_))
                | (SchedulerType::DpWrap(_), SchedulerType::DpWrap(_))
                | (
                    SchedulerType::ClusteredEDF(_, _),
                    SchedulerType::ClusteredEDF(_, _)
                )
                | (SchedulerType::PassiveVp(_), SchedulerType::PassiveVp(_))
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

    /// Return the CPU affinity set if this is a [`SchedulerType::ClusteredEDF`],
    /// [`SchedulerType::ActiveVp`], [`SchedulerType::PassiveVp`], or
    /// [`SchedulerType::MixedVp`] scheduler.
    ///
    /// Returns `Some(set)` where `set` is the set of CPU cores (`1..num_cpu()`) the task
    /// may run on. Returns `None` for all other scheduler variants.
    pub const fn cpu_set(&self) -> Option<CpuSet> {
        match self {
            SchedulerType::ClusteredEDF(_, set) => Some(*set),
            SchedulerType::ActiveVp(set, _) => Some(*set),
            SchedulerType::PassiveVp(set) => Some(*set),
            SchedulerType::MixedVp(active_set, _, passive_set) => {
                Some(active_set.union(*passive_set))
            }
            _ => None,
        }
    }

    /// True if this is a clustered scheduler, i.e. one whose tasks carry a
    /// CPU affinity set. Update this function when adding a new clustered
    /// scheduler; it is the single source of truth for the clustered prefix
    /// of `PRIORITY_LIST`.
    pub const fn is_clustered(&self) -> bool {
        matches!(
            self,
            SchedulerType::ActiveVp(_, _)
                | SchedulerType::MixedVp(_, _, _)
                | SchedulerType::ClusteredEDF(_, _)
                | SchedulerType::PassiveVp(_)
        )
    }

    /// True if this scheduler carries DAG light-pool work (GEDF, and
    /// DAG-Fluid's `DpWrap`). Update this function when adding a further
    /// DAG-oriented global scheduler; it is the single source of truth for
    /// the DAG-pool slice of `PRIORITY_LIST` immediately following the
    /// clustered prefix (see `pool::is_dag_pool_core`).
    pub const fn is_dag_pool_scheduler(&self) -> bool {
        matches!(self, SchedulerType::GEDF(_) | SchedulerType::DpWrap(_))
    }
}

/// # Priority
///
/// `priority()` returns the priority of the scheduler for preemption.
///
/// - The highest priority.
///   - Active-VP scheduler (V-Fed).
/// - The second highest priority.
///   - Mixed active+passive-VP scheduler (V-Fed, Theorem 4). Below
///     `ActiveVp` so a mixed task can never preempt a core's *true*
///     active-VP owner when running there as a mere borrower; above
///     everything else because on its own (possibly partial) active-VP
///     cores it is servicing the same heavy-DAG obligation `ActiveVp`
///     does. Relative order versus `ClusteredEDF`/`PassiveVp`/`GEDF` below
///     has no live scenario to matter for: a specific core is claimed by at
///     most one active-VP owner and lent to at most one passive/mixed
///     borrower at a time (see `dag_sched::policy::vfed`'s pool semantics),
///     so those tiers never actually contend with `MixedVp` for a core —
///     this ordering is chosen for its own sake, not forced by any such
///     contention.
/// - The third highest priority.
///   - Clustered EDF scheduler.
/// - The fourth highest priority.
///   - Passive-VP scheduler (V-Fed). Below `ClusteredEDF` because a
///     passive-VP's whole premise is "leftover capacity", lower priority
///     than any exclusive cluster reservation elsewhere; Federated and
///     V-Fed are alternative policies rarely live in the same run, so this
///     relative ordering mostly matters for `PriorityInfo`'s packed
///     cross-tier comparisons, not for any scenario where they actually
///     contend for the same core.
/// - The fifth highest priority.
///   - GEDF scheduler.
/// - The sixth highest priority.
///   - DAG-Fluid's `DpWrap` scheduler. Below `GEDF` (both DAG-pool
///     schedulers, see `is_dag_pool_scheduler`) for the same reason
///     `PassiveVp` sits below `ClusteredEDF`: Federated/Laxity (`GEDF`) and
///     DAG-Fluid (`DpWrap`) are alternative policies that never run in the
///     same build (mutually exclusive Cargo features), so this relative
///     ordering has no live contention scenario to matter for.
/// - The seventh highest priority.
///   - Prioritized FIFO scheduler.
/// - The eighth highest priority.
///   - Prioritized Round-Robin scheduler.
/// - The lowest priority.
///   - Panicked scheduler.
static PRIORITY_LIST: [SchedulerType; 9] = [
    SchedulerType::ActiveVp(CpuSet::empty(), 0),
    SchedulerType::MixedVp(CpuSet::empty(), 0, CpuSet::empty()),
    SchedulerType::ClusteredEDF(0, CpuSet::empty()),
    SchedulerType::PassiveVp(CpuSet::empty()),
    SchedulerType::GEDF(0),
    SchedulerType::DpWrap(0),
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

// `get_next_task` and its per-pool queue-counter accounting rely on the
// clustered schedulers forming a strict prefix of `PRIORITY_LIST`. Reject
// any reorder at compile time.
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

/// Return the number of DAG-pool schedulers (currently just GEDF)
/// immediately following the clustered prefix of `PRIORITY_LIST`.
const fn get_num_dag_pool_schedulers() -> usize {
    let mut count = 0;
    let start = get_num_clustered_schedulers();
    while start + count < PRIORITY_LIST.len() {
        if PRIORITY_LIST[start + count].is_dag_pool_scheduler() {
            count += 1;
        } else {
            break;
        }
    }
    count
}

// `get_next_task`'s DAG-pool/regular-pool split relies on the DAG-pool
// schedulers forming a strict prefix of PRIORITY_LIST's non-clustered tail.
// Reject any reorder at compile time, mirroring the clustered-prefix check
// above.
const _: () = {
    let mut i = get_num_clustered_schedulers() + get_num_dag_pool_schedulers();
    while i < PRIORITY_LIST.len() {
        assert!(
            !PRIORITY_LIST[i].is_dag_pool_scheduler(),
            "DAG-pool schedulers must form a strict prefix of PRIORITY_LIST immediately after the clustered prefix"
        );
        i += 1;
    }
};

/// When false, no scheduler requests preemption, and `wake_task` enqueues the woken task.
/// `no_preempt` compiles out the IPI handler that runs preemption-pending tasks.
/// Without this flag, a pending task waits until its target CPU goes idle and starves while every worker keeps polling.
pub(crate) const PREEMPTION_ENABLED: bool = cfg!(not(feature = "no_preempt"));

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

    // A CPU reserved by a clustered task's cpu_set (see
    // `task::NUM_CLUSTERED_TASKS_ALIVE`/`task::is_cpu_reserved`) — e.g. a
    // Federated heavy DAG's exclusive cluster — must never run a
    // global-policy (GEDF/PrioritizedFIFO/PrioritizedRR/Panicked) task, even
    // while its clustered queue is momentarily empty. Otherwise unrelated
    // traffic could occupy a core another DAG's schedulability analysis
    // already counted on being exclusive. Global-policy tasks therefore run
    // only on the complement of every reserved core.
    let cpu_id = awkernel_lib::cpu::cpu_id();
    if crate::task::is_cpu_reserved(cpu_id) {
        return None;
    }

    // Skip the clustered prefix: it was either just tried above and returned
    // None (the queue state cannot change in between because both `wake_task`
    // and `get_next_task` hold `GLOBAL_WAKE_GET_MUTEX`), or the counter was 0
    // and its queues are empty. This also structurally guarantees that the
    // per-pool decrements below never apply to a clustered task, which is
    // counted by `NUM_CLUSTERED_TASKS_IN_QUEUE` instead.
    //
    // Within that remainder, the DAG pool (GEDF) and the regular pool
    // (PrioritizedFIFO/RR/Panicked) are further split by cpu_id (see
    // `pool::is_dag_pool_core`/`is_regular_pool_core`): a DAG-pool core
    // may only serve DAG-pool entries, a regular-pool core only regular-pool
    // entries. While the split is inactive (too few workers), both
    // predicates are true everywhere, so every entry is tried on every core
    // — identical to the pre-split behavior.
    let dag_pool_start = get_num_clustered_schedulers();
    let dag_pool_end = dag_pool_start + get_num_dag_pool_schedulers();
    let may_run_dag_pool = pool::is_dag_pool_core(cpu_id);
    let may_run_regular_pool = pool::is_regular_pool_core(cpu_id);

    PRIORITY_LIST[dag_pool_start..]
        .iter()
        .enumerate()
        .find_map(|(offset, scheduler_type)| {
            let is_dag_pool_entry = dag_pool_start + offset < dag_pool_end;
            if is_dag_pool_entry {
                if !may_run_dag_pool {
                    return None;
                }
            } else if !may_run_regular_pool {
                return None;
            }

            let task = get_scheduler(scheduler_type).get_next(execution_ensured)?;

            // Decrement whichever counter this task was queued under (see
            // `Task::wake`), matching the pool it just came from.
            if is_dag_pool_entry {
                crate::task::NUM_DAG_POOL_TASK_IN_QUEUE.fetch_sub(1, Ordering::Relaxed);
            } else {
                crate::task::NUM_REGULAR_POOL_TASK_IN_QUEUE.fetch_sub(1, Ordering::Relaxed);
            }

            Some(task)
        })
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
        SchedulerType::DpWrap(_) => &dp_wrap::SCHEDULER,
        SchedulerType::ClusteredEDF(_, _) => &clustered_edf::SCHEDULER,
        SchedulerType::ActiveVp(_, _) => &active_vp::SCHEDULER,
        SchedulerType::MixedVp(_, _, _) => &mixed_vp::SCHEDULER,
        SchedulerType::PassiveVp(_) => &passive_vp::SCHEDULER,
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

    /// Take the inner value and decrement the counters.
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
    base_time: Instant,
}

impl SleepingTasks {
    const fn new() -> Self {
        Self {
            delta_list: DeltaList::Nil,
            base_time: Instant::zero(),
        }
    }

    /// `dur` is a Duration.
    fn sleep_task(&mut self, handler: Box<dyn FnOnce() + Send>, mut dur: Duration) {
        if self.delta_list.is_empty() {
            self.base_time = Instant::now();
        } else {
            let diff = self.base_time.elapsed();
            dur += diff;
        }

        self.delta_list.insert(dur.as_nanos() as u64, handler);
    }

    /// Sleep until `next` (no relative duration).
    fn sleep_until_task(&mut self, handler: Box<dyn FnOnce() + Send>, next: Instant) {
        if self.delta_list.is_empty() {
            self.base_time = Instant::now();
        }
        let dur = next - self.base_time;

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

/// After reaching `next` time, `sleep_until_handler` will be invoked.
pub(crate) fn sleep_until_task(sleep_handler: Box<dyn FnOnce() + Send>, next: Instant) {
    {
        let mut node = MCSNode::new();
        let mut guard = SLEEPING.lock(&mut node);
        guard.sleep_until_task(sleep_handler, next);
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
    // Check whether each running task exceeds the time quantum (RR) or its
    // active-VP budget (V-Fed) — see `active_vp`'s WCET contract for the
    // bound on this loop's per-cpu work.
    //
    // Only the RR quantum check preempts, so only it is skipped when
    // preemption is disabled. The active-VP budget accounting and the
    // DAG-Fluid switch plan below never send an IPI themselves, and
    // `get_next` gating relies on them either way.
    for cpu_id in 1..num_cpu() {
        if let Some(task_id) = get_current_task(cpu_id) {
            match get_scheduler_type_by_task_id(task_id) {
                Some(SchedulerType::PrioritizedRR(_)) => {
                    if PREEMPTION_ENABLED {
                        prioritized_rr::SCHEDULER.invoke_preemption_tick(cpu_id, task_id)
                    }
                }
                Some(SchedulerType::ActiveVp(_, _)) => active_vp::tick_budget(cpu_id),
                // Only while running as this group's own active-VP work —
                // running here as a mere borrower of some *other* DAG's
                // passive-VP falls through to the `_` arm below, exactly
                // like a plain `PassiveVp` task already does, which is
                // correct: budget belongs to the core's true owner, not to
                // whoever it's currently lent to.
                Some(SchedulerType::MixedVp(active_set, _, _)) if active_set.contains(cpu_id) => {
                    active_vp::tick_budget(cpu_id)
                }
                _ => active_vp::mark_idle(cpu_id),
            }
        } else {
            active_vp::mark_idle(cpu_id);
        }

        // DAG-Fluid's own intra-DP migration switch points (see
        // `dp_wrap::tick_switch_plan`'s own doc): independent of whichever
        // scheduler is currently running on `cpu_id` above -- entitlement
        // can legitimately change out from under a task belonging to some
        // *other* scheduler entirely (e.g. a regular-pool task happening
        // to occupy what is, from DAG-Fluid's perspective, a DAG-pool
        // core mid-switch), and `apply_entitlement`'s own forced-preemption
        // path already only acts when a concrete DpWrap successor is ready
        // and preemption is enabled.
        dp_wrap::tick_switch_plan(cpu_id);
    }

    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.wake_task();
    guard.time_to_wait()
}
