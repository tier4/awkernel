//! DP-WRAP's core computation (Funk, Levin, Sadowski, Pye, Brandt, "DP-FAIR:
//! a unifying theory for optimal hard real-time multiprocessor scheduling",
//! Real-Time Systems 2011, Section 4.2): McNaughton's wrap-around algorithm,
//! used here as DAG-Fluid's real dispatch mechanism within one Deadline
//! Partition (DP) -- the piece the Phase 0/1/2 placeholder dispatch (plain
//! `GEDF` over `dag_sched::resource`'s shared pool) stands in for. See
//! `dag_sched::dp_partition`'s own module doc for how DP boundaries are
//! detected; this module is what should run once a boundary fires, not yet
//! wired into live dispatch (see [`wrap_blocks`]'s own doc for what is and
//! isn't implemented so far).
//!
//! # The algorithm, transcribed from the primary source (Section 4.2)
//!
//! "To schedule jobs in σj, make a 'block' of length δi for each Ti, and
//! line these blocks up along a number line (in any order), starting at
//! zero. Their total length will be no more than m. Split this stack of
//! blocks into length 1 chunks at 1, 2, ..., m − 1, and assign each chunk
//! to its own processor. Each length 1 chunk of tasks represents the
//! scheduling of tasks on the respective processor; tasks which are sliced
//! in two migrate between their two processors [...] To find the actual
//! timing points of context switches [...] within any σj, multiply each
//! length 1 segment by Lj."
//!
//! For DAG-Fluid, each "task" `Ti` in the quote above is one currently-
//! active segment of one admitted DAG-Fluid DAG, and `δi` is that
//! segment's own execution rate `θ_i,j` (`dag_fluid::SegmentSchedule::rate`,
//! computed in Phase 1) rather than a whole periodic task's density -- the
//! DP-FAIR paper's `δi = ei/min(pi,Di)` and DAG-Fluid's `θ_i,j` play the
//! same structural role (a fraction of one processor a unit of work is
//! entitled to for the duration of one scheduling interval), which is why
//! the same wrap-around construction applies directly.
//!
//! # WCET note
//! By explicit user direction (this is a measurement probe for the paper's
//! theory-vs-reality discussion, not a WCET-proven dispatch mechanism --
//! see `dag_sched::dp_partition`'s own module doc for the same scope
//! decision), this module does not carry a proven WCET bound. It stays
//! allocation-bounded and panic-free regardless: [`wrap_blocks`] allocates
//! exactly `m` `Vec`s up front (`(0..m).map(...)`, no further reallocation
//! beyond ordinary `Vec::push` growth bounded by `densities.len()`), and
//! every arithmetic path is on plain `f64` (no indexing that can panic: the
//! `proc >= m` case is checked and simply stops emitting further blocks
//! rather than indexing out of bounds -- reachable only if the *caller*
//! violates the `Σdensities <= m` precondition, at which point silently
//! dropping the remainder here is the same "defensive, not expected"
//! posture `dag_fluid::heavy_capacity_and_deadline` documents for its own
//! analogous precondition).

use super::{
    get_priority, peek_preemption_pending, push_preemption_pending, Scheduler, SchedulerType, Task,
    GLOBAL_WAKE_GET_MUTEX, PREEMPTION_ENABLED,
};
use crate::{
    dag::calculate_and_update_dag_deadline,
    task::{
        get_task, get_task_running, get_tasks_running, set_current_task, set_need_preemption,
        State, MAX_TASK_PRIORITY,
    },
};
use alloc::{
    collections::{BTreeMap, BinaryHeap},
    sync::Arc,
    vec::Vec,
};
use array_macro::array;
use awkernel_lib::{
    cpu::NUM_MAX_CPU,
    sync::mutex::{MCSNode, Mutex},
    time::Instant,
};
use core::{
    cmp::max,
    sync::atomic::{AtomicU32, Ordering},
};

/// McNaughton's wrap-around algorithm. `densities` are `(BlockId, density)`
/// pairs in the order to lay them along the number line (Funk et al.'s "in
/// any order" -- see this module's own doc for what `density` means for a
/// DAG-Fluid segment); `Σdensity <= m` is the caller's precondition (the
/// same shared-pool admission check `dag_sched::resource::reserve_dagfluid_capacity`
/// already enforces).
///
/// Returns one `Vec` per processor (`result.len() == m`, `result[p]` is
/// processor `p`'s own dispatch order), each an ordered list of `(index
/// into densities, start, end)`. `start`/`end` are offsets *within that
/// processor's own unit-length chunk* (`0.0..=1.0`), not yet multiplied by
/// the DP's own length `Lj` -- the paper's own "except for this last
/// multiplication, all calculations can be done once as a preprocessing
/// step" (Sect. 4.2); the caller scales by `Lj` (see this module's own
/// tests for a worked example of both steps together).
pub fn wrap_blocks(densities: &[(usize, f64)], m: usize) -> Vec<Vec<(usize, f64, f64)>> {
    let mut result: Vec<Vec<(usize, f64, f64)>> = (0..m).map(|_| Vec::new()).collect();
    let mut pos = 0.0_f64;

    for &(id, density) in densities {
        let mut remaining = density;
        while remaining > 0.0 {
            let proc = pos as usize;
            if proc >= m {
                // Caller violated the `Σdensity <= m` precondition -- see
                // this module's own doc for why this is a defensive stop,
                // not a panic.
                break;
            }
            let chunk_offset = pos - proc as f64;
            let space_in_chunk = 1.0 - chunk_offset;
            let take = remaining.min(space_in_chunk);
            result[proc].push((id, chunk_offset, chunk_offset + take));
            remaining -= take;
            pos += take;
        }
    }

    result
}

/// DAG-Fluid's real dispatch (`SchedulerType::DpWrap`): a task's own CPU
/// affinity is not fixed at spawn time (unlike `ClusteredEDF`/`ActiveVp`)
/// -- it is *which DAG a CPU is currently entitled to*, recomputed by
/// [`recompute_and_apply`] every time `dag_sched::dp_partition` advances a
/// Deadline Partition (see that module's own doc for when that happens,
/// and this module's own doc for the per-DP-not-per-migration-instant
/// scope decision). Once a CPU is entitled to `dag_id`, any of that DAG's
/// own ready nodes may run there -- entitlement is per-DAG, not per
/// individual node or per-segment (see this crate's own design discussion
/// in `applications/rd_gen_to_dags/src/dag_fluid.rs`'s
/// `segment_completion_gates` doc for why per-segment tracking was ruled
/// out: a node's own execution can legitimately span more than one
/// segment).
const NO_DAG: u32 = u32::MAX;

/// Per-CPU: the `dag_id` this CPU is currently entitled to, or [`NO_DAG`].
/// Read by [`DpWrapScheduler::get_next`] (a plain array load, O(1),
/// alloc-free, panic-free), written only by [`recompute_and_apply`] (boot
/// admission and Deadline-Partition-boundary time, not itself RT-critical
/// dispatch-path code, though it is called from timer-interrupt context —
/// see `dag_sched::dp_partition::on_dp_boundary`'s own WCET note).
static ENTITLEMENT: [AtomicU32; NUM_MAX_CPU] = array![_ => AtomicU32::new(NO_DAG); NUM_MAX_CPU];

/// The `dag_id` `cpu_id` is currently entitled to, if any.
pub(crate) fn entitlement_of(cpu_id: usize) -> Option<u32> {
    match ENTITLEMENT.get(cpu_id) {
        Some(slot) => match slot.load(Ordering::Relaxed) {
            NO_DAG => None,
            dag_id => Some(dag_id),
        },
        None => None,
    }
}

/// One ready DAG-Fluid node, queued under its own `dag_id` (see
/// [`DpWrapData`]). Ordering is identical to `gedf::GEDFTask`'s (same
/// `(absolute_deadline, node_priority, wake_time)` key, smaller
/// `absolute_deadline` first) -- reused verbatim rather than re-derived,
/// since within one DAG's own ready pool the tie-break rationale is the
/// same one GEDF already documents.
struct DpWrapTask {
    task: Arc<Task>,
    absolute_deadline: u64,
    node_priority: u64,
    wake_time: u64,
}

impl PartialOrd for DpWrapTask {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for DpWrapTask {
    fn eq(&self, other: &Self) -> bool {
        self.absolute_deadline == other.absolute_deadline
            && self.node_priority == other.node_priority
            && self.wake_time == other.wake_time
    }
}

impl Ord for DpWrapTask {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        match other.absolute_deadline.cmp(&self.absolute_deadline) {
            core::cmp::Ordering::Equal => match self.node_priority.cmp(&other.node_priority) {
                core::cmp::Ordering::Equal => other.wake_time.cmp(&self.wake_time),
                ord => ord,
            },
            ord => ord,
        }
    }
}

impl Eq for DpWrapTask {}

/// One ready-queue per `dag_id`, rather than one global queue (GEDF) or one
/// queue per fixed `CpuSet` (ClusteredEDF): the entitled CPU set for a
/// given `dag_id` changes over time (see [`ENTITLEMENT`]), but the queue of
/// *that DAG's own* ready nodes does not need to move when it does.
struct DpWrapData {
    queues: BTreeMap<u32, BinaryHeap<DpWrapTask>>,
}

impl DpWrapData {
    fn new() -> Self {
        Self {
            queues: BTreeMap::new(),
        }
    }
}

pub struct DpWrapScheduler {
    data: Mutex<Option<DpWrapData>>,
    priority: u8,
}

impl Scheduler for DpWrapScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let (wake_time, absolute_deadline, node_priority, dag_id) = {
            let mut node_inner = MCSNode::new();
            let mut info = task.info.lock(&mut node_inner);
            let dag_info = info.get_dag_info();
            match info.scheduler_type {
                SchedulerType::DpWrap(dag_id) => {
                    let wake_time = awkernel_lib::delay::uptime();
                    let (absolute_deadline, node_priority) = if let Some(ref dag_info) = dag_info {
                        (
                            calculate_and_update_dag_deadline(dag_info, wake_time, info.state),
                            crate::dag::get_node_priority(dag_info.dag_id, dag_info.node_id),
                        )
                    } else {
                        // Every `DpWrap` task is a DAG-Fluid node and should
                        // always carry `dag_info` -- defensive fallback
                        // mirroring GEDF's own "no dag_info" arm rather than
                        // panicking on a should-never-happen case.
                        (wake_time, 0)
                    };

                    task.priority
                        .update_priority_info(self.priority, MAX_TASK_PRIORITY - absolute_deadline);
                    info.update_absolute_deadline(absolute_deadline);

                    (wake_time, absolute_deadline, node_priority, dag_id)
                }
                _ => unreachable!(),
            }
        };

        let mut node = MCSNode::new();
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);
        if !self.invoke_preemption(task.clone(), dag_id) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data.lock(&mut node_inner);
            let internal_data = data.get_or_insert_with(DpWrapData::new);
            internal_data
                .queues
                .entry(dag_id)
                .or_default()
                .push(DpWrapTask {
                    task: task.clone(),
                    absolute_deadline,
                    node_priority,
                    wake_time,
                });
        }
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let cpu_id = awkernel_lib::cpu::cpu_id();
        let dag_id = entitlement_of(cpu_id)?;

        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);
        let data = (*data).as_mut()?;
        let queue = data.queues.get_mut(&dag_id)?;

        loop {
            let task = queue.pop()?;

            {
                let mut node = MCSNode::new();
                let mut task_info = task.task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }

                if task_info.state == State::Preempted {
                    task_info.need_preemption = false;
                }
                if execution_ensured {
                    task_info.state = State::Running;
                    set_current_task(awkernel_lib::cpu::cpu_id(), task.task.id);
                }
            }

            return Some(task.task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::DpWrap(0)
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

pub static SCHEDULER: DpWrapScheduler = DpWrapScheduler {
    data: Mutex::new(None),
    priority: get_priority(&SchedulerType::DpWrap(0)),
};

impl DpWrapScheduler {
    /// Same shape as `gedf::GEDFScheduler::invoke_preemption`, restricted to
    /// CPUs currently entitled to `dag_id` (see [`ENTITLEMENT`]) rather than
    /// every running CPU -- a `DpWrap` task must never preempt a CPU that
    /// some *other* DAG currently owns the entitlement for.
    fn invoke_preemption(&self, task: Arc<Task>, dag_id: u32) -> bool {
        if !PREEMPTION_ENABLED {
            return false;
        }

        let tasks_running = get_tasks_running()
            .into_iter()
            .filter(|rt| rt.task_id != 0) // Filter out idle CPUs.
            .collect::<alloc::vec::Vec<_>>();

        if tasks_running.iter().any(|rt| rt.task_id == task.id) {
            return false;
        }

        // An idle CPU currently entitled to `dag_id` will pick this task up
        // on its own next `get_next` poll; no forced preemption needed.
        let entitled_idle_cpu_exists = (1..awkernel_lib::cpu::num_cpu())
            .any(|cpu| entitlement_of(cpu) == Some(dag_id) && get_task_running(cpu).task_id == 0);
        if entitled_idle_cpu_exists {
            return false;
        }

        let preemption_target = tasks_running
            .iter()
            .filter(|rt| {
                !crate::task::is_cpu_reserved(rt.cpu_id)
                    && entitlement_of(rt.cpu_id) == Some(dag_id)
            })
            .filter_map(|rt| {
                get_task(rt.task_id).map(|t| {
                    let highest_pending = peek_preemption_pending(rt.cpu_id).unwrap_or(t.clone());
                    (max(t, highest_pending), rt.cpu_id)
                })
            })
            .min();

        let Some((target_task, target_cpu)) = preemption_target else {
            return false;
        };
        if task.preempts(&target_task) {
            push_preemption_pending(target_cpu, task);
            let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
            set_need_preemption(target_task.id, target_cpu);
            awkernel_lib::interrupt::send_ipi(preempt_irq, target_cpu as u32);
            return true;
        }

        false
    }
}

/// Recompute the current Deadline Partition's per-CPU entitlement from
/// every currently-active DAG-Fluid segment's own `(dag_id, concurrency,
/// rate)` (`rate` = that segment's `theta_i,j`, `concurrency` = `m_i,j`
/// interchangeable virtual threads -- see
/// `crate::dag_sched::policy::dag_fluid::SegmentSchedule`'s own doc), and apply it
/// for the Deadline Partition running from `dp_start` until `dp_end`
/// (`None` if no further boundary is currently known -- see below).
/// Called by `dag_sched::dp_partition` once a Deadline Partition boundary
/// is actually acted on (its own completion-gate having been satisfied —
/// see that module's own doc for why advancing is gated on real node
/// completion, not just the theoretical deadline).
///
/// Each virtual thread becomes one entry in [`wrap_blocks`]'s `densities`
/// list (`dag_id` pushed `concurrency` times), so a segment with
/// `concurrency > 1` can legitimately land on more than one processor at
/// once -- real parallelism, matching that segment's own concurrency (see
/// this crate's own worked example in code review discussion: a segment
/// with two ready sibling nodes and two entitled CPUs runs both at once,
/// each CPU independently popping one from the DAG's shared ready queue).
///
/// # Intra-DP migration
/// Every processor's own [`wrap_blocks`] output (not just its largest
/// block) is converted into absolute-time [`SwitchPoint`]s by scaling
/// each block's `(start_frac, end_frac)` by `L_j = dp_end - dp_start` (the
/// paper's own "multiply each length 1 segment by Lj", Sect. 4.2) and
/// adding `dp_start`, so a block [`wrap_blocks`] splits across two
/// processors (a "migrating" block, in the paper's own terms) really does
/// migrate: each processor gets its own slice at its own scheduled
/// instant, not an approximation. The first point is applied immediately
/// (task context, right here); the rest are queued in [`SWITCH_PLAN`] for
/// [`tick_switch_plan`] to apply as their own times arrive.
///
/// If `dp_end` is `None` (no further segment boundary is currently
/// pending -- e.g. every admitted DAG has exhausted its own segments) or
/// the computed `L_j` is zero (defensive: `dp_start`/`dp_end` come from
/// two separate reads of the clock/`PENDING` a caller took without a
/// shared lock across both, so a same-instant race is possible even if
/// unlikely), there is no meaningful interval to schedule migration
/// within -- falls back to one flat entitlement for whichever block holds
/// the *larger* of its shares, [`wrap_blocks`]'s own precondition-violation
/// posture aside.
///
/// # WCET note
/// Bounded by `active.len()` (at most the number of currently-admitted
/// DAG-Fluid DAGs) times each one's own `concurrency` for the `densities`
/// build, then by `pool.len()` (at most `num_cpu()`) for [`wrap_blocks`]
/// and the apply loop, each processor's own switch-point count further
/// bounded by `densities.len()` (`wrap_blocks`' own contract); allocates
/// (`Vec` growth), but only ever from `dag_sched::dp_partition`'s own
/// `advance_due_segments` -- ordinary task context, never a timer-interrupt
/// callback (see that module's own "Split design" doc for why that
/// distinction matters here) -- so this shares that function's "not
/// WCET-proven" scope note without the interrupt-context hazard its own
/// history warns about.
pub fn recompute_and_apply(active: &[(u32, u32, f64)], dp_start: Instant, dp_end: Option<Instant>) {
    let mut slot_table: alloc::vec::Vec<u32> = alloc::vec::Vec::new();
    let mut densities: alloc::vec::Vec<(usize, f64)> = alloc::vec::Vec::new();
    for &(dag_id, concurrency, rate) in active {
        for _ in 0..concurrency {
            densities.push((slot_table.len(), rate));
            slot_table.push(dag_id);
        }
    }

    let pool: alloc::vec::Vec<usize> = crate::dag_sched::resource::dagfluid_pool_cpu_set()
        .iter()
        .collect();
    if pool.is_empty() {
        return;
    }

    let plan = wrap_blocks(&densities, pool.len());

    let l_j = dp_end.and_then(|end| {
        let d = end.saturating_duration_since(dp_start);
        (!d.is_zero()).then_some(d)
    });

    for (proc, &cpu_id) in pool.iter().enumerate() {
        let blocks = plan.get(proc).cloned().unwrap_or_default();

        let Some(duration) = l_j else {
            // No known DP end, or zero-length -- flat entitlement for the
            // larger of this processor's (at most two, per `wrap_blocks`'
            // own contract) shares, same as before intra-DP migration
            // existed.
            let winner = blocks.iter().max_by(|a, b| {
                (a.2 - a.1)
                    .partial_cmp(&(b.2 - b.1))
                    .unwrap_or(core::cmp::Ordering::Equal)
            });
            let new_dag = winner.map(|&(slot_idx, _, _)| slot_table[slot_idx]);
            if let Some(slot) = SWITCH_PLAN.get(cpu_id) {
                let mut node = MCSNode::new();
                slot.lock(&mut node).clear();
            }
            apply_entitlement(cpu_id, new_dag);
            continue;
        };

        let mut switch_points: alloc::vec::Vec<SwitchPoint> = blocks
            .iter()
            .map(|&(slot_idx, start_frac, _end_frac)| SwitchPoint {
                at: dp_start + duration.mul_f64(start_frac),
                dag_id: slot_table[slot_idx],
            })
            .collect();

        let first = if switch_points.is_empty() {
            None
        } else {
            Some(switch_points.remove(0))
        };

        if let Some(slot) = SWITCH_PLAN.get(cpu_id) {
            let mut node = MCSNode::new();
            *slot.lock(&mut node) = switch_points;
        }
        apply_entitlement(cpu_id, first.map(|sp| sp.dag_id));
    }
}

/// One planned entitlement change within the current Deadline Partition,
/// in absolute time (`at`) -- see [`recompute_and_apply`]'s own doc.
struct SwitchPoint {
    at: Instant,
    dag_id: u32,
}

/// Per-CPU: this CPU's own remaining intra-DP switch points for the
/// *current* Deadline Partition, soonest first ([`recompute_and_apply`]
/// replaces the whole `Vec` wholesale on every recompute, so a stale
/// entry from a previous DP can never linger). Like
/// `dag_sched::dp_partition`'s own `PENDING`/`CURRENT`, only this module's
/// own code (`recompute_and_apply`, [`tick_switch_plan`]) ever touches
/// this -- never shared with ordinary DAG/task-graph code -- but unlike
/// that reasoning matters for, this lock is only ever taken from ordinary
/// task/kernel-loop context in the first place ([`tick_switch_plan`] is
/// called from `scheduler::wake_task`'s own per-cpu loop, itself plain
/// non-interrupt code running from the primary CPU's main loop -- see
/// that function's own doc), so no interrupt-context hazard applies here
/// regardless.
static SWITCH_PLAN: [Mutex<alloc::vec::Vec<SwitchPoint>>; NUM_MAX_CPU] =
    array![_ => Mutex::new(alloc::vec::Vec::new()); NUM_MAX_CPU];

/// Apply `cpu_id`'s own next scheduled intra-DP entitlement switch
/// ([`SWITCH_PLAN`]), if its time has arrived. Called once per
/// `scheduler::wake_task` tick for every worker CPU (see that function's
/// own per-cpu loop) -- ordinary, non-interrupt context, the same
/// guarantee `dag_sched::dp_partition::advance_due_segments` relies on
/// for its own DAG/task lookups (see that module's own "Split design"
/// doc); [`apply_entitlement`]'s forced-preemption path is exactly as
/// safe to run from here as it already is from `recompute_and_apply`.
///
/// WCET note: one `SWITCH_PLAN[cpu_id]` lock, O(1) front-check, and (only
/// when due) an O(n) `Vec::remove(0)` bounded by that processor's own
/// remaining switch-point count for the current DP (small in practice --
/// bounded by the number of currently-active DAG-Fluid segments); no
/// panic (`.get`/`.first()`, no direct indexing).
pub(crate) fn tick_switch_plan(cpu_id: usize) {
    let Some(slot) = SWITCH_PLAN.get(cpu_id) else {
        return;
    };

    let due = {
        let mut node = MCSNode::new();
        let mut queue = slot.lock(&mut node);
        let now = Instant::now();
        match queue.first() {
            Some(sp) if sp.at <= now => Some(queue.remove(0)),
            _ => None,
        }
    };

    if let Some(sp) = due {
        apply_entitlement(cpu_id, Some(sp.dag_id));
    }
}

/// Apply one CPU's new entitlement decision from [`recompute_and_apply`],
/// forcing a preemption only when a concrete successor task is already
/// in hand -- never an unconditional "stop whatever is running" (see
/// `scheduler::active_vp::tick_budget`'s own doc for the reproduced hang
/// that pattern caused in `task::preempt::do_preemption`: it only
/// context-switches when `PREEMPTION_PENDING_TASKS` holds a specific
/// successor, so pushing a preemption request with none in mind can strand
/// the displaced task forever).
fn apply_entitlement(cpu_id: usize, new_dag: Option<u32>) {
    let Some(slot) = ENTITLEMENT.get(cpu_id) else {
        return;
    };

    let mut node = MCSNode::new();
    let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);

    let old = slot.swap(new_dag.unwrap_or(NO_DAG), Ordering::Relaxed);
    let old_dag = if old == NO_DAG { None } else { Some(old) };
    if old_dag == new_dag {
        return;
    }
    log::info!(
        "dp_wrap: CPU#{cpu_id} entitlement {old_dag:?} -> {new_dag:?} at {:?}",
        Instant::now()
    );
    let Some(dag_id) = new_dag else {
        return;
    };

    let running = get_task_running(cpu_id);
    if running.task_id == 0 {
        // Idle: nudge it to re-poll `get_next_task` now, rather than wait
        // for `task::wake_workers`'s own next pass.
        awkernel_lib::cpu::wake_cpu(cpu_id);
        return;
    }

    // Without preemption the successor popped below would be stranded in
    // the pending queue; the running task keeps the CPU and the entitled
    // DAG's node is picked up by `get_next` once it yields.
    if !PREEMPTION_ENABLED {
        return;
    }

    if let Some(t) = get_task(running.task_id) {
        let mut node2 = MCSNode::new();
        if t.info.lock(&mut node2).get_dag_info().map(|d| d.dag_id) == Some(dag_id) {
            // Already running dag_id's own work (e.g. entitlement moved
            // away and immediately back) -- nothing to do.
            return;
        }
    }

    let mut node_inner = MCSNode::new();
    let mut data = SCHEDULER.data.lock(&mut node_inner);
    let Some(data) = data.as_mut() else {
        return;
    };
    let Some(queue) = data.queues.get_mut(&dag_id) else {
        return;
    };
    let Some(successor) = queue.pop() else {
        // No ready node for the newly-entitled DAG yet -- leave the
        // current task running rather than force a switch with no
        // successor in hand (see this function's own doc).
        return;
    };

    push_preemption_pending(cpu_id, successor.task);
    let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
    set_need_preemption(running.task_id, cpu_id);
    awkernel_lib::interrupt::send_ipi(preempt_irq, cpu_id as u32);
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    /// Funk et al.'s own worked example (Fig. 7): seven tasks with
    /// densities `[0.3, 0.5, 0.5, 0.6, 0.5, 0.4, 0.2]` (summing to
    /// exactly `3 = m`) on 3 processors, lined up in that order. Hand
    /// re-derived from the paper's own algorithm description (Sect. 4.2)
    /// independently of the figure's pixels, then cross-checked against
    /// the figure's own textual claims: "Task 3 migrates from Processor 2
    /// to Processor 1" and "Task 5 migrates from Processor 3 to Processor
    /// 2" (1-indexed in the paper; tasks 3 and 5 are indices 2 and 4
    /// here) -- i.e. each migrating task runs at the *end* of its first
    /// processor's chunk and the *start* of its second, matching "tasks
    /// which migrate are run at the beginning of the slice on one
    /// processor, and at the end on the other" (Sect. 4.2).
    #[test]
    fn test_wrap_blocks_matches_paper_worked_example() {
        let densities: Vec<(usize, f64)> = vec![
            (0, 0.3),
            (1, 0.5),
            (2, 0.5),
            (3, 0.6),
            (4, 0.5),
            (5, 0.4),
            (6, 0.2),
        ];
        let result = wrap_blocks(&densities, 3);
        assert_eq!(result.len(), 3);

        // `f64` accumulation (`pos += take`) leaves the usual last-bit
        // rounding noise (e.g. `0.30000000000000004`), so compare with a
        // tolerance rather than `assert_eq!` on the tuples directly.
        fn assert_close(actual: &[(usize, f64, f64)], expected: &[(usize, f64, f64)]) {
            assert_eq!(actual.len(), expected.len());
            for (&(aid, astart, aend), &(eid, estart, eend)) in actual.iter().zip(expected) {
                assert_eq!(aid, eid);
                assert!((astart - estart).abs() < 1e-9, "{astart} vs {estart}");
                assert!((aend - eend).abs() < 1e-9, "{aend} vs {eend}");
            }
        }

        assert_close(&result[0], &[(0, 0.0, 0.3), (1, 0.3, 0.8), (2, 0.8, 1.0)]);
        assert_close(&result[1], &[(2, 0.0, 0.3), (3, 0.3, 0.9), (4, 0.9, 1.0)]);
        assert_close(&result[2], &[(4, 0.0, 0.4), (5, 0.4, 0.8), (6, 0.8, 1.0)]);

        // Every block's total assigned time (summed across whichever
        // processor(s) it landed on) equals its own density -- Sect. 4.2's
        // own invariant ("their total length will be no more than m").
        let mut totals = [0.0_f64; 7];
        for proc in &result {
            for &(id, start, end) in proc {
                totals[id] += end - start;
            }
        }
        for (id, &(_, expected_density)) in densities.iter().enumerate() {
            assert!((totals[id] - expected_density).abs() < 1e-9, "block {id}");
        }
    }

    /// A block that fits entirely within one processor's chunk (no
    /// migration) is a single `(id, 0.0, density)` entry there and
    /// nowhere else.
    #[test]
    fn test_wrap_blocks_single_task_no_migration() {
        let densities = vec![(0, 0.5)];
        let result = wrap_blocks(&densities, 2);
        assert_eq!(result[0], vec![(0, 0.0, 0.5)]);
        assert_eq!(result[1], vec![]);
    }

    /// Scaling step (the paper's own "multiply each length 1 segment by
    /// Lj"): with a DP of length `Lj = 10`, processor 0's chunk from the
    /// worked example above becomes absolute-within-DP offsets
    /// `[0, 3), [3, 8), [8, 10)`.
    #[test]
    fn test_scaling_by_slice_length() {
        let densities: Vec<(usize, f64)> = vec![(0, 0.3), (1, 0.5), (2, 0.5)];
        let result = wrap_blocks(&densities, 1);
        let l_j = 10.0_f64;
        let scaled: Vec<(usize, f64, f64)> = result[0]
            .iter()
            .map(|&(id, s, e)| (id, s * l_j, e * l_j))
            .collect();
        assert_eq!(scaled, vec![(0, 0.0, 3.0), (1, 3.0, 8.0), (2, 8.0, 10.0)]);
    }
}
