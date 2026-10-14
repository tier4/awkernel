//! V-Fed's active-VP scheduler ([`crate::dag_sched::policy::vfed`]): the
//! highest-priority tier, one exclusive slot per core in a heavy DAG's
//! active-VP group. Reuses [`super::clustered_edf`]'s cpu_set-restricted
//! affinity queue and `invoke_preemption` pattern verbatim for the actual
//! dispatch/migration/preemption mechanics (an active-VP group behaves
//! exactly like a `ClusteredEDF` cluster there — greedy, work-conserving,
//! preemption and migration freely allowed among the group's own cores),
//! and adds two things `ClusteredEDF` does not need:
//!
//! - A strict preference for the group's *leading* core (the paper's rule:
//!   a non-leading core may only take active-VP work while the leading
//!   core is busy). Enforced entirely on the *pop* side, in
//!   [`ActiveVpScheduler::get_next`] — not by restricting which cpu_set an
//!   entry is *pushed* with, which cannot correctly express "leading may
//!   still be idle when a second vertex becomes eligible while leading is
//!   already serving a first one". Both a task's own `wake_task` and every
//!   core's `get_next` hold `GLOBAL_WAKE_GET_MUTEX`, so `get_next`'s check
//!   of "is my group's leading core currently running something" is
//!   race-free.
//! - A replenishable per-job execution budget per core that forces the
//!   served task off a core once exhausted (see [`tick_budget`]), freeing
//!   that core for a complementary passive-VP (`super::passive_vp`, not
//!   yet implemented — see that module's doc for why this scheduler alone
//!   does not yet complete V-Fed's mechanism).
//!
//! # WCET contract (tick path: [`tick_budget`], [`mark_idle`])
//! - No heap allocation.
//! - No blocking, no `.await`.
//! - Bounded: O(1) per call (fixed-size per-cpu array access only).
//! - Never panics for any `cpu_id < NUM_MAX_CPU` (the only caller,
//!   [`crate::scheduler::wake_task`]'s per-cpu loop, already bounds it that
//!   way); out-of-range ids are rejected via `.get()`, not indexed.
//! - Does not log, format, or call user code.

use super::{
    get_priority, peek_preemption_pending, push_preemption_pending, ClusteredTask, Scheduler,
    SchedulerType, Task, GLOBAL_WAKE_GET_MUTEX, PREEMPTION_ENABLED,
};
use crate::atomic_u64::AtomicU64;
use crate::{
    dag::{calculate_and_update_dag_deadline, is_job_release_wake},
    task::{
        get_task, get_task_running, set_current_task, set_need_preemption, State, MAX_TASK_PRIORITY,
    },
};
use affinity_btree_queue::{AffinityBTreeQueue, DEFAULT_MIN_DEGREE};
use alloc::sync::Arc;
use array_macro::array;
use awkernel_lib::{
    cpu::{masked_workers, num_cpu, CpuSet, CPU_SET_WORDS, NUM_MAX_CPU},
    sync::mutex::{MCSNode, Mutex},
};
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

/// Sentinel `LEADING_OF` value meaning "this core is not currently part of
/// any active-VP group." Not a valid cpu id (bounded well below
/// `NUM_MAX_CPU`), so it can never be confused with a real leading cpu.
const NO_GROUP: usize = usize::MAX;

/// For each core currently part of an active-VP group, the leading core of
/// *that* group (a core maps to itself if it *is* the leading one).
/// `NO_GROUP` if `cpu` is not currently part of any active-VP group. Kept
/// up to date from [`ActiveVpScheduler::wake_task`] (derived from the
/// waking task's own `SchedulerType::ActiveVp`, so it never drifts from
/// what admission decided) rather than a separate admission-time setter,
/// so this module has a single place that writes it.
static LEADING_OF: [AtomicUsize; NUM_MAX_CPU] =
    array![_ => AtomicUsize::new(NO_GROUP); NUM_MAX_CPU];

/// The leading core of `cpu`'s active-VP group, or `None` if `cpu` is not
/// currently part of one.
fn leading_of(cpu: usize) -> Option<usize> {
    match LEADING_OF.get(cpu) {
        Some(leading) => match leading.load(Ordering::Relaxed) {
            NO_GROUP => None,
            leading => Some(leading),
        },
        None => None,
    }
}

/// Record `cpu`'s group's leading core. Called from this module's own
/// `wake_task` (the whole `cpu_set`) and from
/// [`super::mixed_vp::MixedVpScheduler::wake_task`] (only the mixed task's
/// own `active_set` — never its borrowed `passive_set`, which belongs to a
/// *different* DAG's active-VP group and must keep whatever leading core
/// *that* DAG already recorded here).
pub(crate) fn set_leading(cpu: usize, leading_cpu: usize) {
    if let Some(slot) = LEADING_OF.get(cpu) {
        slot.store(leading_cpu, Ordering::Relaxed);
    }
}

/// Whether `cpu` may take active-VP work *right now*: budget remaining, and
/// — if `cpu` is a non-leading member of a group whose leading core is
/// currently idle — deferring to the paper's leading-preference rule (see
/// the module doc). Shared by [`ActiveVpScheduler::get_next`] and
/// [`super::mixed_vp::MixedVpScheduler::get_next`]'s own-active-core branch:
/// a mixed group's active portion is budget/leading-gated exactly like a
/// pure active-VP group's, since [`set_initial_budget`] and [`set_leading`]
/// are called identically for both (`dag_sched::policy::vfed` never
/// distinguishes pure vs. mixed when arming a claimed active core).
pub(crate) fn active_eligible(cpu_id: usize) -> bool {
    if !has_budget(cpu_id) {
        return false;
    }
    if let Some(leading) = leading_of(cpu_id) {
        if leading != cpu_id && get_task_running(leading).task_id == 0 {
            return false;
        }
    }
    true
}

/// Each active-VP core's initial (replenish-to) budget, in nanoseconds. `0`
/// means "no active-VP group currently claims this core." Set once by
/// [`set_initial_budget`] when `vfed` admits a heavy DAG's active-VP group
/// (mirrors `task::NUM_CLUSTERED_TASKS_ALIVE`: per-cpu metadata fixed at
/// admission/spawn time, read continuously by the scheduler).
static INITIAL_BUDGET: [AtomicU64; NUM_MAX_CPU] = array![_ => AtomicU64::new(0); NUM_MAX_CPU];

/// Each active-VP core's remaining budget for the *current* job. Replenished
/// to `INITIAL_BUDGET[cpu]` at job release (see [`replenish`]), decremented
/// as the served task executes there (see [`tick_budget`]). `0` blocks
/// further dispatch onto this core until the next replenishment (see
/// [`ActiveVpScheduler::get_next`]).
static BUDGET_REMAINING: [AtomicU64; NUM_MAX_CPU] = array![_ => AtomicU64::new(0); NUM_MAX_CPU];

/// Nanosecond timestamp `tick_budget` last measured elapsed time from, per
/// core. Distinct from a task's own `last_executed_time` (task.rs): that
/// resets on every redispatch, so it cannot by itself accumulate a job's
/// *total* consumption across a preemption-then-resume; this instead
/// tracks per-tick deltas, reset only on an idle-to-running transition (see
/// [`WAS_RUNNING`]) so an idle gap is never charged against the budget.
static LAST_TICK: [AtomicU64; NUM_MAX_CPU] = array![_ => AtomicU64::new(0); NUM_MAX_CPU];

/// Whether `cpu`'s active-VP was known to be running as of the last tick.
static WAS_RUNNING: [AtomicBool; NUM_MAX_CPU] = array![_ => AtomicBool::new(false); NUM_MAX_CPU];

/// Claim `cpu` for an active-VP group with initial (per-job) budget
/// `budget_ns`, and arm its remaining budget so it is immediately usable
/// (equivalent to the group's first job having just been released). Called
/// once per core by `dag_sched::policy::vfed` when it admits a heavy DAG's
/// active-VP group.
pub(crate) fn set_initial_budget(cpu: usize, budget_ns: u64) {
    let Some(initial) = INITIAL_BUDGET.get(cpu) else {
        return;
    };
    initial.store(budget_ns, Ordering::Relaxed);
    if let Some(remaining) = BUDGET_REMAINING.get(cpu) {
        remaining.store(budget_ns, Ordering::Relaxed);
    }
}

/// Release `cpu` from active-VP duty (its DAG was torn down), so a later
/// admission can reuse it without inheriting a stale budget.
///
/// No caller yet: nothing in this codebase tears a DAG down once admitted
/// (the same gap `dag_sched::resource::release_cluster` documents for
/// Federated's cluster release). Kept ready for when that exists, rather
/// than added later as an afterthought once budgets can already go stale.
#[allow(dead_code)]
pub(crate) fn release_budget(cpu: usize) {
    if let Some(initial) = INITIAL_BUDGET.get(cpu) {
        initial.store(0, Ordering::Relaxed);
    }
    if let Some(remaining) = BUDGET_REMAINING.get(cpu) {
        remaining.store(0, Ordering::Relaxed);
    }
    if let Some(leading) = LEADING_OF.get(cpu) {
        leading.store(NO_GROUP, Ordering::Relaxed);
    }
}

/// Replenish every core in `cpu_set` to its `INITIAL_BUDGET`. Called at job
/// release (see [`is_job_release_wake`]).
pub(crate) fn replenish(cpu_set: CpuSet) {
    for cpu in cpu_set.iter() {
        if let (Some(initial), Some(remaining)) =
            (INITIAL_BUDGET.get(cpu), BUDGET_REMAINING.get(cpu))
        {
            remaining.store(initial.load(Ordering::Relaxed), Ordering::Relaxed);
        }
    }
}

/// True if `cpu` currently has active-VP budget remaining (i.e. is not
/// exhausted for the current job). Also true for a core with no active-VP
/// at all (`INITIAL_BUDGET[cpu] == 0`), since "no active-VP here" must not
/// block anything — only genuine exhaustion (armed but spent) should.
fn has_budget(cpu: usize) -> bool {
    let Some(remaining) = BUDGET_REMAINING.get(cpu) else {
        return false;
    };
    let Some(initial) = INITIAL_BUDGET.get(cpu) else {
        return false;
    };
    initial.load(Ordering::Relaxed) == 0 || remaining.load(Ordering::Relaxed) > 0
}

/// Called once per tick (see the module's WCET contract) for `cpu_id` when
/// its currently-running task is *not* an active-VP task: resets the
/// idle-to-running edge detector so the next time an active-VP task runs
/// there, the gap while idle is not charged against its budget.
pub(crate) fn mark_idle(cpu_id: usize) {
    if let Some(was_running) = WAS_RUNNING.get(cpu_id) {
        was_running.store(false, Ordering::Relaxed);
    }
}

/// Called once per tick for `cpu_id` while an active-VP task is currently
/// running there: charge the elapsed time since the last tick against
/// `cpu_id`'s remaining budget. See the module's WCET contract.
///
/// Deliberately does **not** force an IPI-driven preemption when the
/// budget reaches 0 here — see the "soft cap" note below. Enforcement is
/// instead "soft": [`ActiveVpScheduler::get_next`] already refuses to
/// dispatch anything new onto a budget-exhausted core (`has_budget`), and
/// a task's own next cooperative yield point (an `.await` inside its
/// future, which every well-behaved task must have anyway to be
/// schedulable at all) is when it actually loses the core. A task
/// mid-poll when its budget expires can therefore run somewhat past
/// `θz` — bounded by its own poll-to-poll granularity, not by this
/// function — which is a real gap from the paper's exact-budget model,
/// tracked as follow-up work once a safer forced-preemption path exists.
///
/// # Why not force it here
/// An earlier version called `awkernel_lib::interrupt::send_ipi` (mirroring
/// `PrioritizedRR::invoke_preemption_tick`) to preempt the running task the
/// moment its budget hit 0. Under QEMU this reproducibly **hung** two
/// active-VP tasks sharing one group: the IPI's handler
/// (`task::preempt::do_preemption`) only performs a real context-switch
/// when `scheduler::PREEMPTION_PENDING_TASKS[cpu_id]` holds a *specific*
/// successor task to hand the core to (mirroring `invoke_preemption`'s "a
/// higher-priority arrival displaces a victim" use case) — but budget
/// expiry has no such successor in mind, only "stop now". Pushing
/// whatever `get_next_task(false)` happened to find (often the sibling
/// active-VP task itself) meant the displaced task was parked in
/// `task::preempt::PREEMPTED_TASKS[cpu_id]`, which is only drained by
/// `re_schedule()` on that *same* cpu's *next* preemption-driven context
/// switch — not guaranteed to ever happen, so the parked task could go
/// unwoken forever. Reproduced with `applications/tests/test_active_vp`
/// (two tasks, budgets small enough to exhaust within the test): both
/// tasks stopped mid-run and never resumed. Fixed by removing the forced
/// preemption rather than by chasing the exact successor-task semantics
/// `do_preemption` needs, given the risk of a missed-wakeup hang in RT
/// scheduler code outweighs the precision lost by a soft cap.
pub(crate) fn tick_budget(cpu_id: usize) {
    let (Some(last_tick), Some(was_running), Some(remaining)) = (
        LAST_TICK.get(cpu_id),
        WAS_RUNNING.get(cpu_id),
        BUDGET_REMAINING.get(cpu_id),
    ) else {
        return;
    };

    let now = awkernel_lib::delay::uptime();

    if !was_running.swap(true, Ordering::Relaxed) {
        // Just started running (again) after being idle or serving a
        // different scheduler class; don't charge the gap.
        last_tick.store(now, Ordering::Relaxed);
        return;
    }

    let previous = last_tick.swap(now, Ordering::Relaxed);
    let elapsed = now.saturating_sub(previous);
    let before = remaining.load(Ordering::Relaxed);
    remaining.store(before.saturating_sub(elapsed), Ordering::Relaxed);
}

/// The run queue for non-leading active-VP cores: same key/ordering as
/// `ClusteredEDF` (see that module), reused verbatim — ordering among one
/// task's own vertices does not affect correctness here (the paper does
/// not restrict it), but reusing the identical key avoids a second,
/// pointlessly-different comparator.
type ActiveVpQueue = AffinityBTreeQueue<
    (u64, u64, u64),
    ClusteredTask<Arc<Task>>,
    DEFAULT_MIN_DEGREE,
    CPU_SET_WORDS,
>;

pub struct ActiveVpScheduler {
    data: Mutex<Option<ActiveVpQueue>>,
    priority: u8,
}

impl Scheduler for ActiveVpScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let (wake_time, absolute_deadline, node_priority, cpu_set, leading_cpu) = {
            let mut node_inner = MCSNode::new();
            let mut info = task.info.lock(&mut node_inner);
            let dag_info = info.get_dag_info();
            match info.scheduler_type {
                SchedulerType::ActiveVp(cpu_set, leading_cpu) => {
                    let wake_time = awkernel_lib::delay::uptime();
                    let (absolute_deadline, node_priority) = if let Some(ref dag_info) = dag_info {
                        if is_job_release_wake(dag_info, info.state) {
                            replenish(cpu_set);
                        }
                        (
                            calculate_and_update_dag_deadline(dag_info, wake_time, info.state),
                            crate::dag::get_node_priority(dag_info.dag_id, dag_info.node_id),
                        )
                    } else {
                        (wake_time, 0)
                    };

                    task.priority
                        .update_priority_info(self.priority, MAX_TASK_PRIORITY - absolute_deadline);
                    info.update_absolute_deadline(absolute_deadline);

                    (
                        wake_time,
                        absolute_deadline,
                        node_priority,
                        cpu_set,
                        leading_cpu,
                    )
                }
                _ => unreachable!(),
            }
        };

        if cpu_set.is_empty() || masked_workers(cpu_set, num_cpu()) != cpu_set {
            unreachable!("ActiveVp: cpu_set {cpu_set:?} was not normalized by spawn");
        }

        // Keep `LEADING_OF` current for every core in this group — cheap
        // (bounded by the group's size, a handful of cores) and derived
        // straight from this task's own `SchedulerType`, so it can never
        // drift from what admission decided.
        for cpu in cpu_set.iter() {
            set_leading(cpu, leading_cpu);
        }

        let mut node = MCSNode::new();
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);

        // No leading-vs-non-leading distinction here: both are equally
        // valid *push* targets (the preference is enforced at *pop* time
        // instead — see `get_next` — because only that side can
        // race-freely observe "is leading busy right now", per the
        // `GLOBAL_WAKE_GET_MUTEX` this function and `get_next` share).
        // Otherwise identical to `ClusteredEDF::wake_task`: prefer an
        // immediate targeted preemption over enqueuing when one is needed
        // (e.g. a passive-VP is currently using a now-eligible core; V-Fed
        // active-VPs always outrank it via `PriorityInfo`'s packed
        // scheduler-class tier).
        if !self.invoke_preemption(task.clone()) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data.lock(&mut node_inner);
            let queue = data.get_or_insert_with(|| ActiveVpQueue::new(num_cpu()));
            let _ = queue.push(
                (absolute_deadline, u64::MAX - node_priority, wake_time),
                cpu_set,
                ClusteredTask::new(task.clone()),
            );
        }
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        // Budget, and (for a non-leading core) the leading-preference rule
        // (paper's rule — see the module doc); race-free because
        // `wake_task` (the only other place `RUNNING`/this scheduler's
        // queue state changes) holds the same `GLOBAL_WAKE_GET_MUTEX`
        // `get_next_task` already does.
        if !active_eligible(cpu_id) {
            return None;
        }

        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);
        let queue = (*data).as_mut()?;

        loop {
            let (_, _, mut entry) = queue.pop_for_cpu(cpu_id)?;
            let Some(task) = entry.take() else {
                continue;
            };

            {
                let mut node = MCSNode::new();
                let mut task_info = task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }
                if task_info.state == State::Preempted {
                    task_info.need_preemption = false;
                }
                if execution_ensured {
                    task_info.state = State::Running;
                    set_current_task(cpu_id, task.id);
                }
            }

            return Some(task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::ActiveVp(CpuSet::empty(), 0)
    }

    fn priority(&self) -> u8 {
        self.priority
    }

    fn queued_cpu_mask(&self) -> CpuSet {
        let mut node = MCSNode::new();
        let data = self.data.lock(&mut node);
        match &*data {
            Some(queue) => queue.affinity_mask(),
            None => CpuSet::empty(),
        }
    }
}

pub static SCHEDULER: ActiveVpScheduler = ActiveVpScheduler {
    data: Mutex::new(None),
    priority: get_priority(&SchedulerType::ActiveVp(CpuSet::empty(), 0)),
};

impl ActiveVpScheduler {
    /// Identical in structure to `ClusteredEDFScheduler::invoke_preemption`
    /// (see that module): find the lowest-priority running-or-pending
    /// victim across `task`'s cpu_set and preempt it if `task` outranks it.
    /// Active-VP tasks always outrank whatever this can find in practice —
    /// a passive-VP task once `passive_vp` exists, or nothing at all today
    /// — via `PriorityInfo`'s packed scheduler-class tier, but the
    /// comparison is kept general rather than hard-coded to that fact.
    fn invoke_preemption(&self, task: Arc<Task>) -> bool {
        if !PREEMPTION_ENABLED {
            return false;
        }

        let cpu_set = task.cpu_set.expect("Task has no CPU set");

        let mut victim: Option<(usize, Arc<Task>)> = None;

        for cpu_id in cpu_set.iter() {
            let task_running = get_task_running(cpu_id);

            if task_running.task_id == task.id {
                return false;
            }
            if task_running.task_id == 0 {
                return false;
            }

            let task_running = get_task(task_running.task_id);
            let task_pending = peek_preemption_pending(cpu_id);

            let target_task = match (task_running, task_pending) {
                (Some(running), Some(pending)) => running.max(pending),
                (Some(running), None) => running,
                (None, Some(pending)) => pending,
                (None, None) => return false,
            };

            match victim {
                Some((_, ref lowest)) if target_task >= *lowest => (),
                _ => victim = Some((cpu_id, target_task)),
            }
        }

        let Some((victim_cpu, target_task)) = victim else {
            return false;
        };

        if task > target_task {
            push_preemption_pending(victim_cpu, task);
            let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
            set_need_preemption(target_task.id, victim_cpu);
            awkernel_lib::interrupt::send_ipi(preempt_irq, victim_cpu as u32);
            return true;
        }

        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_and_replenish_budget() {
        set_initial_budget(200, 5_000);
        assert!(has_budget(200));

        // Drain it directly to simulate consumption, then confirm
        // replenish restores it.
        BUDGET_REMAINING[200].store(0, Ordering::Relaxed);
        assert!(!has_budget(200));

        replenish(CpuSet::empty().with(200));
        assert!(has_budget(200));

        release_budget(200);
        assert!(has_budget(200)); // "no active-VP here" reads as available
    }

    #[test]
    fn test_has_budget_true_when_no_active_vp_claimed() {
        // A core never claimed by `set_initial_budget` (INITIAL_BUDGET == 0)
        // must never block dispatch — only genuine exhaustion should.
        assert!(has_budget(201));
    }

    #[test]
    fn test_tick_budget_does_not_charge_idle_gap() {
        set_initial_budget(202, 1_000_000_000); // 1s, plenty of headroom
        mark_idle(202);
        // First tick after being idle: primes LAST_TICK, charges nothing.
        tick_budget(202);
        let after_first = BUDGET_REMAINING[202].load(Ordering::Relaxed);
        assert_eq!(after_first, 1_000_000_000);
    }

    #[test]
    fn test_leading_of_defaults_to_no_group() {
        // A core never assigned to any active-VP group.
        assert_eq!(leading_of(210), None);
    }

    #[test]
    fn test_leading_of_reflects_group_membership() {
        LEADING_OF[211].store(211, Ordering::Relaxed); // leading maps to itself
        LEADING_OF[212].store(211, Ordering::Relaxed); // non-leading maps to leading
        assert_eq!(leading_of(211), Some(211));
        assert_eq!(leading_of(212), Some(211));

        release_budget(211);
        assert_eq!(leading_of(211), None);
    }
}
