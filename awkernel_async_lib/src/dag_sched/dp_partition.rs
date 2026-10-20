//! System-wide Deadline-Partition boundary tracking and real dispatch
//! entitlement (real-machine DAG-Fluid): every DAG-Fluid task's own
//! per-segment absolute deadline (computed at admission time — see
//! `crate::dag_sched::policy::dag_fluid`'s own module doc for Algorithm 1 lines
//! 16–21, the 2022 paper's Section 8 thread-list conversion) is
//! registered here once, before dispatch begins. Two independent
//! consumers then watch [`PENDING`]:
//!
//! - [`on_dp_boundary`] (a `TimerRequestId::DpBoundary` interrupt
//!   callback): fires exactly at each boundary's theoretical deadline and
//!   logs the measurement this module is named for (scheduled vs. actual
//!   time) — nothing else. It never mutates a segment's completion state
//!   and never touches [`CURRENT`] or the DAG/task graph (see "Split
//!   design" below for why).
//! - [`advance_due_segments`] (an ordinary background task, spawned by
//!   [`spawn_advancer`]): polls [`PENDING`] on a short, fixed cadence
//!   ([`ADVANCER_POLL_INTERVAL`]) and, once a due boundary's own
//!   *completion gate* is satisfied (see below), advances that DAG's
//!   current segment and calls `scheduler::dp_wrap::recompute_and_apply`
//!   to recompute the real per-CPU entitlement for the new Deadline
//!   Partition.
//!
//! # Completion gate: advance is gated on real work, not just the clock
//! The papers' segment deadlines are assigned with *zero* slack by
//! construction (`Σd_i,j` sums exactly to the virtual deadline `D*_i` —
//! see `crate::dag_sched::policy::dag_fluid`'s own module doc): the idealized fluid
//! model proves a segment finishes exactly on time if run at its own
//! `theta_i,j` rate continuously, with no margin anywhere. On real
//! hardware, IPI latency, migration cost, and discrete task-switch
//! granularity all eat directly into that zero margin.
//!
//! An earlier design would have advanced strictly on the theoretical
//! clock, reassigning a CPU's entitlement to the *next* segment the
//! instant a boundary's scheduled time passed, regardless of whether the
//! current segment's own work had actually finished — silently abandoning
//! any still-running node with no rescue mechanism. This was explicitly
//! rejected as unacceptable. Instead, each [`BoundaryEntry`] carries a
//! `gate_nodes` list ([`crate::dag_sched::policy::dag_fluid::segment_completion_gates`]'s
//! own output, mapped to the caller's node ids — the nodes the idealized timeline expects to finish
//! exactly at this segment's end): [`advance_due_segments`] only actually
//! advances past a boundary once every node in its gate has really
//! processed at least one period (see [`gate_satisfied_from_cache`]'s own
//! doc for why `DagInfo::period_index`, not `TaskInfo`'s own `State`, is
//! the right signal for this). Until then, the CPU(s) currently
//! entitled to that DAG keep their entitlement (the segment does **not**
//! lose its capacity share), the overrun is logged once, and the boundary
//! is retried on the advancer's own next poll — the gap between
//! "theoretical deadline" and "gate actually satisfied" *is* the
//! theory-vs-reality measurement this module exists to produce, made
//! visible in the log rather than silently absorbed.
//!
//! # Split design: why the gate check cannot run from the timer callback
//! An earlier version ran the completion-gate check (and the subsequent
//! `CURRENT` update / entitlement recompute) directly inside
//! [`on_dp_boundary`]. This reproducibly broke the system: **every**
//! `TimerRequestId::DpBoundary` firing after the first simply stopped
//! happening at all, confirmed with both a blocking `Mutex::lock` and a
//! non-blocking `Mutex::try_lock` for the gate check's own node lookups.
//! Direct experiment isolated this to calling into `Dag`'s graph lock or
//! `TaskInfo`'s own lock from timer-interrupt context specifically: with
//! an empty `gate_nodes` (skipping both), all three of a real test DAG's
//! segments fired correctly with the *same* surrounding code; with a
//! real, non-empty gate, only the first ever fired. The likely mechanism
//! (not fully confirmed): `awkernel_sync`'s `InterruptGuard` (used
//! internally by every `MCSLock::lock`/`try_lock`) calls
//! `voluntary_preemption()` on drop whenever interrupts end up enabled
//! again — appropriate for ordinary task-context code, but not
//! necessarily safe to trigger from inside a timer ISR's own callback
//! chain. `Dag::graph`/`TaskInfo`'s locks are also the *same* locks
//! ordinary task-context code (pub/sub routing, `task::run_main`'s own
//! poll bookkeeping) contends for concurrently — unlike this module's own
//! `PENDING`/`CURRENT` locks, which only this module ever touches and
//! which showed no such issue either from the timer callback or from the
//! advancer task.
//!
//! The fix is this module's current split: [`on_dp_boundary`] touches
//! only [`PENDING`] (proven safe from interrupt context) purely to timestamp
//! *when* each boundary's theoretical deadline was actually observed;
//! every DAG/task lookup (`resolve_gate_period_indices`) and every `CURRENT`/
//! entitlement mutation happens only from [`advance_due_segments`],
//! which never runs from interrupt context.
//!
//! # Scope: not WCET-proven dispatch
//! By explicit user direction, this module does not carry a proven WCET
//! bound on its own callback latency — that latency (and now also gate
//! overrun) is exactly what it measures, not what it guarantees.
//!
//! # Placement: whichever CPU happens to register/arm it
//! `awkernel_lib::timer::request_at` arms whichever CPU calls it (that
//! module's own per-CPU multiplexer design); this module does not enforce
//! any particular placement, only logs which CPU actually did the
//! arming/firing.
//!
//! # Absolute-time baseline
//! Segment deadlines are computed relative to a task's own release time
//! (the papers' `r_i,j`, Section 4.2), but this experimental setup admits
//! every DAG-Fluid task once at boot, before dispatch
//! (`finish_create_dags`) begins — there is no live "job release" event
//! yet to anchor to. [`register_segment`]'s caller-supplied `release`
//! time stands in for it (by convention, `Instant::now()` at admission —
//! see `rd_gen_to_dags::build_dag`'s `dagfluid` arm); this is a
//! documented approximation, not the papers' own semantics.

use alloc::{boxed::Box, collections::BTreeMap, sync::Arc, vec::Vec};
use awkernel_lib::{
    sync::mutex::{MCSNode, Mutex},
    time::Instant,
    timer::{self, TimerRequestId},
};
use core::{
    sync::atomic::{AtomicU32, Ordering},
    time::Duration,
};

/// How often [`advance_due_segments`] polls [`PENDING`] for boundaries
/// whose completion gate has newly cleared. Short enough that a
/// segment's measured "gate satisfied" latency stays close to the real
/// completion time; long enough to be a plain periodic background task
/// rather than a busy-poll.
///
/// 100us, not the original 1ms: this interval is a pure detection-latency
/// tax paid once per segment transition (see [`advance_due_segments`]'s
/// own doc), and with real DAGs commonly decomposing into dozens of
/// segments (see [`crate::dag_sched::policy::dag_fluid::segment_completion_gates`]'s
/// own real-machine trace: 41 segments observed for one DAG), that tax
/// compounds across the whole DAG's lifetime -- up to 1ms * segment count
/// of pure polling overhead on top of the real completion-latency numbers
/// this module measures. 100us keeps the same "plain periodic task, not a
/// busy-poll" character (still a real sleep between polls, not a spin
/// loop) while cutting that per-segment tax by 10x.
const ADVANCER_POLL_INTERVAL: Duration = Duration::from_micros(100);

/// One outstanding segment deadline, not yet advanced past.
struct BoundaryEntry {
    dag_id: u32,
    segment_index: usize,
    /// The absolute time this boundary is scheduled for.
    scheduled: Instant,
    /// `m_i,j`: this segment's own thread count (see
    /// `crate::dag_sched::policy::dag_fluid::SegmentSchedule::concurrency`).
    concurrency: u32,
    /// `theta_i,j`: this segment's own execution rate (see
    /// `crate::dag_sched::policy::dag_fluid::SegmentSchedule::rate`).
    rate: f64,
    /// This segment's own completion gate (see this module's own doc) —
    /// node ids the idealized timeline expects to finish exactly at this
    /// segment's end.
    gate_nodes: Vec<u32>,
    /// Lazily resolved, one slot per `gate_nodes` entry (same order,
    /// same length): that node's own `DagInfo::period_index` handle,
    /// once [`resolve_gate_period_indices`] has managed to look it up
    /// (`None` until then — a node's task may not exist yet the first
    /// few times this is checked, since [`register_segment`] runs before
    /// `register_dag_nodes` spawns the actual tasks). Cached rather than
    /// re-resolved every poll: `period_index` is `Arc<AtomicU32>`, so once
    /// cached, checking it is a lock-free atomic load, needing no further
    /// `Dag`/`Task` lock acquisition at all — see
    /// [`gate_satisfied_from_cache`]'s own doc for why this is a safer
    /// completion signal than `TaskInfo`'s own `State` in the first
    /// place.
    gate_period_indices: Vec<Option<Arc<AtomicU32>>>,
    /// Set by [`on_dp_boundary`] once it has logged this entry's
    /// scheduled-vs-actual latency measurement, so a repeat timer fire
    /// (or the timer simply never being re-armed for it again, see that
    /// function's own doc) never logs the same entry twice.
    logged: bool,
    /// Set by [`advance_due_segments`] once it has logged this entry's
    /// completion-gate overrun, so repeated polls while still blocked
    /// don't spam the log every [`ADVANCER_POLL_INTERVAL`].
    warned_overrun: bool,
}

static PENDING: Mutex<Vec<BoundaryEntry>> = Mutex::new(Vec::new());

/// Per-`dag_id`: the `(concurrency, rate)` of that DAG's own *currently
/// active* segment — i.e. the one whose entitlement
/// `scheduler::dp_wrap::recompute_and_apply` should currently be granting
/// CPU time to. Seeded by [`register_segment`] for segment 0, advanced by
/// [`on_dp_boundary`] once a segment's completion gate clears, and removed
/// once a DAG's last segment clears (nothing left to entitle).
static CURRENT: Mutex<BTreeMap<u32, (u32, f64)>> = Mutex::new(BTreeMap::new());

/// Convert a segment's relative-deadline/release-offset value (`f64`,
/// milliseconds — the unit `rd_gen_to_dags`'s own `time_unit` default
/// feature uses) into a `Duration`. Truncates towards zero rather than
/// rounding: `f64::round`/`ceil` need `std`/`libm`, unavailable in this
/// crate's `no_std` build — the same constraint
/// `crate::dag_sched::policy::dag_fluid` documents for its own float-to-integer
/// conversions (`ceil_capacity_to_cores`). Negative input (should not
/// occur for a real offset/deadline) clamps to zero rather than
/// wrapping.
fn millis_f64_to_duration(ms: f64) -> Duration {
    Duration::from_millis(ms.max(0.0) as u64)
}

/// Register one segment's own absolute deadline (`release +
/// offset_ms + duration_ms`, both in milliseconds — `offset_ms` from
/// `crate::dag_sched::policy::dag_fluid::segment_release_offsets`, `duration_ms`
/// from that same segment's own `SegmentSchedule::relative_deadline`)
/// for `dag_id`, along with the `(concurrency, rate)` DP-Wrap density this
/// segment contributes (see `scheduler::dp_wrap::recompute_and_apply`'s
/// own doc) and its own completion gate (`gate_nodes` — see
/// [`crate::dag_sched::policy::dag_fluid::segment_completion_gates`]). Called once per
/// segment, in increasing `segment_index` order, at DAG-Fluid admission
/// time (boot, non-RT), before [`arm_next`]/dispatch begins. `segment_index
/// == 0` also seeds [`CURRENT`] with this segment's own density, since a
/// DAG's first segment is active from release with no boundary of its own
/// to advance past. `Vec::push`/`BTreeMap` insertion (possibly
/// reallocating) is fine here: this only ever runs during boot admission,
/// never from [`on_dp_boundary`].
#[allow(clippy::too_many_arguments)]
pub fn register_segment(
    dag_id: u32,
    segment_index: usize,
    release: Instant,
    offset_ms: f64,
    duration_ms: f64,
    concurrency: u32,
    rate: f64,
    gate_nodes: Vec<u32>,
) {
    let scheduled = release + millis_f64_to_duration(offset_ms + duration_ms);
    let gate_period_indices = alloc::vec![None; gate_nodes.len()];
    let mut node = MCSNode::new();
    let mut pending = PENDING.lock(&mut node);
    pending.push(BoundaryEntry {
        dag_id,
        segment_index,
        scheduled,
        concurrency,
        rate,
        gate_nodes,
        gate_period_indices,
        logged: false,
        warned_overrun: false,
    });
    drop(pending);

    if segment_index == 0 {
        let mut node = MCSNode::new();
        let mut current = CURRENT.lock(&mut node);
        current.insert(dag_id, (concurrency, rate));
    }
}

/// Apply [`CURRENT`]'s present contents as the real per-CPU entitlement —
/// call once after every DAG-Fluid DAG has been admitted (segment 0 of
/// each already seeded [`CURRENT`] via [`register_segment`]), before
/// dispatch begins, and again from [`advance_due_segments`] whenever a
/// segment actually advances.
///
/// `dp_start`/`dp_end` bound the Deadline Partition
/// `scheduler::dp_wrap::recompute_and_apply` computes intra-DP migration
/// switch points within: `dp_start` is simply `Instant::now()` (this DP
/// starts the moment its own entitlement is being computed, not the
/// possibly-already-passed theoretical boundary time that triggered this
/// call — see [`advance_due_segments`]'s own doc on why a segment's real
/// completion can lag its theoretical deadline); `dp_end` is the
/// earliest still-pending boundary left in [`PENDING`] after this
/// update, i.e. the next point at which entitlement will need
/// recomputing again, or `None` if nothing remains pending (every
/// admitted DAG has exhausted its own segments).
fn apply_current_entitlement() {
    let active: Vec<(u32, u32, f64)> = {
        let mut node = MCSNode::new();
        let current = CURRENT.lock(&mut node);
        current
            .iter()
            .map(|(&dag_id, &(concurrency, rate))| (dag_id, concurrency, rate))
            .collect()
    };
    let dp_start = Instant::now();
    let dp_end = {
        let mut node = MCSNode::new();
        let pending = PENDING.lock(&mut node);
        pending.iter().map(|e| e.scheduled).min()
    };
    crate::scheduler::dp_wrap::recompute_and_apply(&active, dp_start, dp_end);
}

/// Call once, after every DAG-Fluid DAG has been admitted and every
/// segment registered, to grant each DAG's own segment-0 entitlement
/// before dispatch begins (see `rd_gen_to_dags::lib::run`'s call site,
/// alongside [`arm_next`]).
pub fn apply_initial_entitlement() {
    apply_current_entitlement();
}

/// For each `cached` slot still `None`, try to resolve its gate node's own
/// `DagInfo::period_index` handle and fill it in. Only ever called from
/// [`advance_due_segments`] (ordinary task context) — see this module's
/// own "Split design" doc for why this must never run from
/// [`on_dp_boundary`]'s interrupt context.
///
/// A node's task may not exist yet the first few times this runs
/// (`register_segment` runs before `register_dag_nodes` spawns the
/// actual tasks — see [`BoundaryEntry::gate_period_indices`]'s own doc),
/// so a lookup failing here just leaves that slot `None` for the next
/// poll to retry; already-resolved slots are left untouched (`period_index`
/// is stable for a task's whole lifetime, no need to re-resolve).
fn resolve_gate_period_indices(
    dag_id: u32,
    gate_nodes: &[u32],
    cached: &mut [Option<Arc<AtomicU32>>],
) {
    let Some(dag) = crate::dag::get_dag(dag_id) else {
        return;
    };
    for (slot, &node_id) in cached.iter_mut().zip(gate_nodes) {
        if slot.is_some() {
            continue;
        }
        let Some(task_id) = dag.get_node_task_id(node_id) else {
            continue;
        };
        let Some(task) = crate::task::get_task(task_id) else {
            continue;
        };
        let dag_info = {
            let mut node = MCSNode::new();
            let guard = task.info.lock(&mut node);
            guard.get_dag_info()
        };
        if let Some(dag_info) = dag_info {
            *slot = Some(dag_info.period_index);
        }
    }
}

/// Whether every gate node's own `DagInfo::period_index` (see
/// [`resolve_gate_period_indices`]) shows it has processed at least one
/// period. A `None` slot (not yet resolved: either the task doesn't exist
/// yet, or its very first period hasn't released) counts as **not**
/// satisfied — the same "unknown means not yet done" default
/// [`resolve_gate_period_indices`]'s own doc uses, for the same reason.
///
/// # Why `period_index`, not `TaskInfo`'s own `State`
/// An earlier version checked `State::Terminated`. Confirmed by direct
/// observation once the interrupt-safety redesign above made it possible
/// to actually exercise this against a real DAG: a periodic source
/// reactor (`spawn_periodic_reactor`) loops forever (`interval.tick()
/// .await` each period) and an intermediate/sink reactor loops waiting
/// for its next pub/sub message — neither ever reaches `State::Terminated`
/// during normal steady-state operation (only DAG teardown would do
/// that), so that check could never actually be satisfied.
///
/// `State::Waiting` (idle between releases) was considered instead, but
/// rejected: a reactor sits in `Waiting` both *before* its current
/// period's inputs have arrived and *after* it finishes that period
/// waiting for the next one — the same state value for two opposite
/// answers to "has this period's work been done yet?", which risks a
/// false "satisfied" the moment a node happens to be waiting for its
/// *first* period rather than genuinely done with it.
///
/// `DagInfo::period_index` (already tracked elsewhere for trace
/// labeling) has no such ambiguity: it starts at the explicit sentinel
/// [`crate::task::NO_PERIOD_YET`] and only ever moves forward, exactly
/// once per period actually processed, so "has it moved past
/// `NO_PERIOD_YET`" unambiguously means "has completed at least one
/// period" — the correct signal for this one-shot (admission-time)
/// gate. It is also `Arc<AtomicU32>`, so checking it needs no `Dag`/`Task`
/// lock at all once cached (see [`resolve_gate_period_indices`]).
fn gate_satisfied_from_cache(cached: &[Option<Arc<AtomicU32>>]) -> bool {
    cached.iter().all(|slot| match slot {
        Some(period_index) => period_index.load(Ordering::Acquire) != crate::task::NO_PERIOD_YET,
        None => false,
    })
}

/// Arm the timer for the earliest still-*unlogged* boundary, if any (see
/// [`on_dp_boundary`]'s own doc for why "unlogged" rather than "still
/// pending"). Safe to call repeatedly — a no-op if nothing qualifies, and
/// idempotent otherwise (re-arming for the same soonest deadline is
/// harmless, `awkernel_lib::timer::request_at`'s own contract).
pub fn arm_next() {
    let next = {
        let mut node = MCSNode::new();
        let pending = PENDING.lock(&mut node);
        pending
            .iter()
            .filter(|e| !e.logged)
            .map(|e| e.scheduled)
            .min()
    };
    if let Some(deadline) = next {
        log::info!(
            "dp_partition: arming DpBoundary on CPU#{} for t={:?}",
            awkernel_lib::cpu::cpu_id(),
            deadline
        );
        timer::request_at(TimerRequestId::DpBoundary, deadline);
    }
}

/// The `TimerRequestId::DpBoundary` callback (see [`install`]). Purely a
/// measurement probe (see this module's own "Split design" doc): for
/// every not-yet-[`logged`](BoundaryEntry::logged) entry whose scheduled
/// time has actually arrived, logs the measured latency (`Instant::now()`
/// at fire time minus its own `scheduled` time) alongside which CPU
/// observed it, and marks it logged so a later re-check (or the timer
/// simply not being re-armed for it again) never logs it twice. Takes no
/// action on the entry otherwise — no DAG/task lookup, no `CURRENT`
/// mutation, no entitlement recompute; that is entirely
/// [`advance_due_segments`]'s job.
///
/// Re-arms for the earliest still-unlogged entry, if any (see
/// [`arm_next`]) — once every currently-registered entry has been
/// logged, this simply stops re-arming until [`register_segment`] adds a
/// new one; [`advance_due_segments`]'s own independent poll loop is what
/// continues to notice and act on already-logged, still-pending entries
/// from here on.
///
/// WCET note (see module doc's "not WCET-proven" scope): bounded by the
/// number of DAG-Fluid segments still registered (only ever shrinks,
/// never regrows after boot admission); no DAG/task lookup, so no risk of
/// the interrupt-context lock hazard this module's own doc describes; no
/// panic (`Instant: Ord`, no direct indexing).
fn on_dp_boundary() {
    let now = Instant::now();

    let mut node = MCSNode::new();
    let mut pending = PENDING.lock(&mut node);
    for entry in pending.iter_mut() {
        if !entry.logged && entry.scheduled <= now {
            let latency = now.saturating_duration_since(entry.scheduled);
            log::info!(
                "dp_partition: DAG#{} segment[{}] DP boundary fired on CPU#{}, scheduled={:?} actual={now:?} latency={latency:?}",
                entry.dag_id,
                entry.segment_index,
                awkernel_lib::cpu::cpu_id(),
                entry.scheduled,
            );
            entry.logged = true;
        }
    }
    let next = pending
        .iter()
        .filter(|e| !e.logged)
        .map(|e| e.scheduled)
        .min();
    drop(pending);

    if let Some(deadline) = next {
        log::info!(
            "dp_partition: arming DpBoundary on CPU#{} for t={:?}",
            awkernel_lib::cpu::cpu_id(),
            deadline
        );
        timer::request_at(TimerRequestId::DpBoundary, deadline);
    }
}

/// A due boundary snapshotted by [`advance_due_segments`]: `(pending index,
/// dag_id, segment_index, gate_nodes, gate_period_indices)`.
type DueEntry = (usize, u32, usize, Vec<u32>, Vec<Option<Arc<AtomicU32>>>);

/// Poll [`PENDING`] once for boundaries whose scheduled time has arrived,
/// and actually advance the ones whose completion gate
/// ([`gate_satisfied_from_cache`]) is satisfied — see this module's own
/// "Split design" doc for why this, and not [`on_dp_boundary`], is where
/// the DAG/task lookups and `CURRENT`/entitlement mutation happen. Called
/// from ordinary (non-interrupt) task context only — see
/// [`spawn_advancer`].
///
/// - **Satisfied**: removed from [`PENDING`], and [`CURRENT`] advanced to
///   whatever segment of that `dag_id` comes next (or removed entirely if
///   this was its last segment).
/// - **Not yet satisfied**: left in [`PENDING`] (with whatever gate
///   handles [`resolve_gate_period_indices`] managed to newly cache
///   written back, so later polls don't redo that resolution); the
///   overrun is logged once (guarded by
///   [`BoundaryEntry::warned_overrun`], so a still-blocked entry doesn't
///   spam the log on every poll).
///
/// [`apply_current_entitlement`] is called once at the end if anything
/// actually advanced.
fn advance_due_segments() {
    let now = Instant::now();

    // Snapshot every due entry's own fields up front (one `PENDING` lock,
    // released before `resolve_gate_period_indices` looks up live
    // DAG/task state, which takes other locks of its own). `gate_nodes`
    // and `gate_period_indices` are cheap to clone (small `Vec`, and
    // `Option<Arc<_>>` clones are just refcount bumps).
    let due: Vec<DueEntry> = {
        let mut node = MCSNode::new();
        let pending = PENDING.lock(&mut node);
        pending
            .iter()
            .enumerate()
            .filter(|(_, e)| e.scheduled <= now)
            .map(|(i, e)| {
                (
                    i,
                    e.dag_id,
                    e.segment_index,
                    e.gate_nodes.clone(),
                    e.gate_period_indices.clone(),
                )
            })
            .collect()
    };

    let mut resolved_indices: Vec<usize> = Vec::new();
    let mut newly_blocked: Vec<usize> = Vec::new();
    let mut cache_updates: Vec<(usize, Vec<Option<Arc<AtomicU32>>>)> = Vec::new();
    for (i, dag_id, _segment_index, gate_nodes, mut cached) in due {
        resolve_gate_period_indices(dag_id, &gate_nodes, &mut cached);
        if gate_satisfied_from_cache(&cached) {
            resolved_indices.push(i);
        } else {
            newly_blocked.push(i);
        }
        cache_updates.push((i, cached));
    }

    if !cache_updates.is_empty() {
        let mut node = MCSNode::new();
        let mut pending = PENDING.lock(&mut node);
        for (i, cached) in cache_updates {
            if let Some(entry) = pending.get_mut(i) {
                entry.gate_period_indices = cached;
            }
        }
    }

    if !newly_blocked.is_empty() {
        let mut node = MCSNode::new();
        let mut pending = PENDING.lock(&mut node);
        for &i in &newly_blocked {
            let Some(entry) = pending.get_mut(i) else {
                continue;
            };
            if !entry.warned_overrun {
                let overrun = now.saturating_duration_since(entry.scheduled);
                log::warn!(
                    "dp_partition: DAG#{} segment[{}] DP boundary overrun on CPU#{}: theoretical deadline passed {overrun:?} ago, completion gate not yet satisfied -- entitlement unchanged, retrying",
                    entry.dag_id,
                    entry.segment_index,
                    awkernel_lib::cpu::cpu_id(),
                );
                entry.warned_overrun = true;
            }
        }
    }

    if resolved_indices.is_empty() {
        return;
    }

    // Highest-index-first so `swap_remove`'s move-the-last-element step
    // can never invalidate an index still queued for removal.
    resolved_indices.sort_unstable_by(|a, b| b.cmp(a));

    let removed: Vec<BoundaryEntry> = {
        let mut node = MCSNode::new();
        let mut pending = PENDING.lock(&mut node);
        resolved_indices
            .iter()
            .map(|&i| pending.swap_remove(i))
            .collect()
    };

    for entry in &removed {
        let completion_latency = now.saturating_duration_since(entry.scheduled);
        log::info!(
            "dp_partition: DAG#{} segment[{}] completion gate satisfied on CPU#{}: theoretical deadline={:?}, gate cleared at {now:?} (completion_latency={completion_latency:?}, warned_overrun_first={})",
            entry.dag_id,
            entry.segment_index,
            awkernel_lib::cpu::cpu_id(),
            entry.scheduled,
            entry.warned_overrun,
        );
    }

    let next_density: BTreeMap<u32, (u32, f64)> = {
        let mut node = MCSNode::new();
        let pending = PENDING.lock(&mut node);
        removed
            .iter()
            .filter_map(|entry| {
                // The entry with the *smallest* `segment_index`, not
                // simply the first one `PENDING`'s own (post-swap_remove)
                // order happens to yield -- `swap_remove` moves whatever
                // was `PENDING`'s own last element into each freed slot,
                // which can leave a *later* segment sitting at an earlier
                // vec position than an untouched *earlier* one. Confirmed
                // by direct QEMU observation: without `min_by_key` here,
                // `CURRENT` could get stuck alternating between two
                // segments that happened to share the same
                // `(concurrency, rate)`, silently never actually reaching
                // the real next segment in between them.
                pending
                    .iter()
                    .filter(|e| e.dag_id == entry.dag_id)
                    .min_by_key(|e| e.segment_index)
                    .map(|e| (entry.dag_id, (e.concurrency, e.rate)))
            })
            .collect()
    };

    {
        let mut node = MCSNode::new();
        let mut current = CURRENT.lock(&mut node);
        for entry in &removed {
            match next_density.get(&entry.dag_id) {
                Some(&density) => {
                    current.insert(entry.dag_id, density);
                }
                None => {
                    current.remove(&entry.dag_id);
                }
            }
        }
    }

    apply_current_entitlement();
}

/// Spawn the background task that drives [`advance_due_segments`] on a
/// fixed [`ADVANCER_POLL_INTERVAL`] cadence, forever. Call once at boot,
/// after [`install`]/[`apply_initial_entitlement`]/[`arm_next`].
///
/// `PrioritizedFIFO(31)` (max, matching `kernel_main.rs`'s own auto-trace/
/// auto-reboot background tasks), not `(0)`: this task's own scheduling
/// delay is *itself* measurement error on top of the real
/// theory-vs-reality numbers it exists to produce, not just an internal
/// implementation detail -- confirmed directly on real hardware, where
/// this task's very first poll after boot was delayed ~54ms behind
/// segment 0's own theoretical deadline (competing for the regular pool
/// with network-service/shell/auto-trace startup work at the original
/// priority 0). Raising it doesn't change *when* `spawn_advancer` itself
/// runs (that's this DAG's own admission order), only how promptly this
/// task, once spawned, wins the regular pool's core against other
/// regular-pool tasks contending for it at the same moment.
pub fn spawn_advancer() {
    crate::task::spawn(
        "dp_wrap advancer".into(),
        async {
            loop {
                advance_due_segments();
                crate::sleep(ADVANCER_POLL_INTERVAL).await;
            }
        },
        crate::scheduler::SchedulerType::PrioritizedFIFO(31),
    );
}

/// Register [`on_dp_boundary`] as `TimerRequestId::DpBoundary`'s
/// callback. Call once at boot, before the first
/// [`register_segment`]/[`arm_next`].
pub fn install() {
    timer::register_timer_callback(TimerRequestId::DpBoundary, Box::new(on_dp_boundary));
}
