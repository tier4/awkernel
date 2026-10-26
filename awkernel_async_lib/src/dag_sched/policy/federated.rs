//! Federated scheduling admission for DAG tasks.
//!
//! # Paper-faithful batch admission ([`admit_batch`] / [`is_batch_feasible`])
//!
//! Three published algorithms, each defined for one class of task system,
//! chosen per task set by [`FederatedVariant::for_task_set`]:
//!
//! | task set        | variant                                  | paper |
//! |-----------------|------------------------------------------|-------|
//! | all `D = T`     | [`FederatedVariant::LiImplicit`]         | Li et al., ECRTS 2014 |
//! | all `D <= T`    | [`FederatedVariant::BaruahConstrained`]  | Baruah, DATE 2015 (`FEDCONS`) |
//! | some `D > T`    | [`FederatedVariant::BaruahArbitrary`]    | Baruah, IPDPS 2015 (`FEDERATED`) |
//!
//! All three share one shape ([`plan_batch`]): each high-density DAG
//! (`δ = C / min(D, T) >= 1`) gets `MINPROCS` processors for its exclusive
//! use; the low-density DAGs are then partitioned, as sequential tasks,
//! onto the processors left over (partitioned EDF, see
//! [`crate::dag_sched::partition`]). What differs is `MINPROCS` (Li's
//! closed form `ceil((C-L)/(D-L))`; Baruah's list-scheduling search for
//! `D <= T` ([`list_schedule_makespan`]); IPDPS 2015's Lemma 1 for
//! `D > T`) and the partitioning condition (IPDPS 2015 adds a utilization
//! check; Li et al. instead admit the low-utilization tasks by
//! `m_low >= 2 * Σ U_low`). The decision is all-or-nothing for the whole task set, like the
//! papers' `return FAILURE`.
//!
//! # Legacy per-DAG admission ([`classify_dag`] / [`admit_dag`])
//!
//! The functions below predate the batch path and are **not** any of the
//! three papers: they admit one DAG at a time, size heavy DAGs by
//! `ceil((C-L)/(D-L))` regardless of deadline type, and put every light DAG
//! on a shared global-EDF pool admitted by total density
//! (`Σ C/min(D, T) <= free cores`), which is not a sufficient test for
//! global EDF. [`classify_dag`] remains useful as a per-DAG feasibility
//! prefilter (it rejects `D < L`). The notes that follow describe that
//! legacy path.
//!
//! Federated Scheduling classifies a DAG by its *density* `C / min(D, T)`
//! (volume over the shorter of relative deadline and period — see
//! [`density_window`]):
//! - **Heavy** (`density > 1`): given an exclusive cluster of `m` cores.
//! - **Light** (`density <= 1`): shares the remaining cores with other light
//!   DAGs, admitted only while the sum of every admitted light DAG's density
//!   still fits the pool (see [`resource::reserve_light_utilization`]) — a
//!   heavy DAG's theorem-backed core count is worthless if the light side is
//!   silently oversubscribed instead.
//!
//! Li et al.'s original design only covers implicit-deadline DAGs (`D = T`),
//! where density and plain utilization `u = C/T` coincide. For a
//! constrained-deadline DAG (`D < T`), using `u = C/T` alone would
//! under-count a DAG whose deadline is tighter than its period: it could
//! read as comfortably light by utilization while still needing an entire
//! core continuously to finish within its shorter deadline window. Using
//! `min(D, T)` throughout (density) instead of `T` alone (utilization)
//! covers both the classical implicit case and Baruah's constrained/
//! arbitrary-deadline generalization with the same formula, since `D >= T`
//! reduces `min(D, T)` back to `T`.
//!
//! This module is admission-time only. It does not add a new run queue or a
//! new [`crate::scheduler::Scheduler`] impl: [`SchedulerType::ClusteredEDF`]
//! already implements "EDF restricted to a `CpuSet`" (cluster reservation,
//! preemption, the lot), so a heavy DAG's cluster is simply a `ClusteredEDF`
//! cpu_set; a light DAG uses [`SchedulerType::ClusteredEDF`] on its partition's
//! single core under [`admit_batch`] (or plain [`SchedulerType::GEDF`] under
//! the legacy [`admit_dag`]). Both already compute a
//! per-job-instance absolute deadline for every node of a DAG via
//! [`crate::dag::calculate_and_update_dag_deadline`], so this module does
//! not duplicate that logic — it only decides *which* scheduler and *which*
//! cores.
//!
//! [`admit_dag`] is the single entry point, taking one [`DagMetrics`]. That
//! config is deliberately the *only* thing admission looks at, so a caller
//! with a fully-known static DAG structure (e.g. `rd_gen_to_dags`, via
//! [`DagMetrics::from_static`]) and a caller who can only supply a human
//! estimate for a dynamically-built DAG (via [`DagMetrics::from_measured`])
//! go through the exact same admission logic — neither path is a special
//! case of the other.

use alloc::vec::Vec;

use awkernel_lib::cpu::CpuSet;

use crate::{
    dag_sched::{
        admission::AdmissionError,
        graph::DagGraph,
        metrics::{DagMetrics, MetricsSource},
        partition::{self, Condition, PackingStrategy, SeqTask},
        precondition::{self, Check, Policy},
        resource,
    },
    scheduler::SchedulerType,
};

/// Result of [`classify_dag`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskClass {
    Light,
    Heavy { required_cores: u16 },
}

/// The `SchedulerType` (and classification metadata) that [`admit_batch`] or
/// [`admit_dag`] decided a DAG's nodes should use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FederatedAssignment {
    pub class: TaskClass,
    pub scheduler_type: SchedulerType,
    /// Carried over from the [`DagMetrics`] that produced this assignment,
    /// so a caller can log/display it without keeping the original config
    /// around.
    pub source: MetricsSource,
}

/// `density = C / window`: a DAG is heavy iff its WCET volume exceeds
/// `window`, which the caller has already narrowed to `min(D, T)` (see
/// [`density_window`]) so this reduces to the classical `u = C/T` test for
/// an implicit/lenient (`D >= T`) DAG.
const fn is_heavy(volume: u64, window: u64) -> bool {
    volume > window
}

/// `min(D, T)`: the interval a DAG's volume must be spread over for the
/// heavy/light density test and the light-pool ledger to remain a valid
/// bound regardless of deadline model (see the module-level doc comment).
const fn density_window(config: &DagMetrics) -> u64 {
    if config.relative_deadline < config.period {
        config.relative_deadline
    } else {
        config.period
    }
}

/// Classify a DAG and, if heavy, compute its required core count. Does not
/// claim any cores; see [`resource::allocate_cluster`] / [`admit_dag`] for
/// that. This legacy per-DAG path uses Li et al.'s core count for any
/// deadline model, so it applies Li's timing preconditions except the
/// implicit-deadline one ([`Check::CriticalPathWithinDeadline`],
/// [`Check::SlackForParallelWork`]); a precondition error reports DAG 0
/// (see [`AdmissionError::with_dag_id`]).
pub fn classify_dag(config: &DagMetrics) -> Result<TaskClass, AdmissionError> {
    Check::CriticalPathWithinDeadline.verify(0, config)?;
    Check::SlackForParallelWork.verify(0, config)?;

    if !is_heavy(config.volume, density_window(config)) {
        return Ok(TaskClass::Light);
    }

    // `None` here only on a core count beyond `u16`.
    let Some(required_cores) = config.min_dedicated_cores() else {
        return Err(AdmissionError::NoFeasibleAllocation);
    };

    Ok(TaskClass::Heavy { required_cores })
}

/// Admit a DAG: classify it and decide the `SchedulerType` every one of its
/// nodes should be registered with. Works identically whether `config` was
/// built via [`DagMetrics::from_static`] or [`DagMetrics::from_measured`].
///
/// - Heavy: claims its exclusive cluster from the shared ledger (release it
///   with [`resource::release_cluster`] once the DAG is torn down, if ever —
///   none of this test bed's DAGs currently are).
/// - Light: commits its utilization against the shared ledger (release it
///   with [`resource::release_light_utilization`] likewise).
pub fn admit_dag(config: DagMetrics) -> Result<FederatedAssignment, AdmissionError> {
    match classify_dag(&config)? {
        TaskClass::Light => {
            let _utilization_scaled =
                resource::reserve_light_utilization(config.volume, density_window(&config))?;
            Ok(FederatedAssignment {
                class: TaskClass::Light,
                scheduler_type: SchedulerType::GEDF(config.relative_deadline),
                source: config.source,
            })
        }
        TaskClass::Heavy { required_cores } => {
            let cores = resource::allocate_cluster(required_cores)?;
            Ok(FederatedAssignment {
                class: TaskClass::Heavy { required_cores },
                scheduler_type: SchedulerType::ClusteredEDF(config.relative_deadline, cores),
                source: config.source,
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Paper-faithful batch admission (three published variants)
// ---------------------------------------------------------------------------

/// Makespan of one dag-job under Graham's (non-preemptive) list scheduling
/// on `processors` identical unit-speed processors, every node executing
/// for exactly its WCET: whenever a processor is idle and some node is
/// available (all predecessors finished), the available node earliest in
/// the priority list starts on it. `None` if `processors == 0` or the graph
/// has a cycle.
pub fn list_schedule_makespan(graph: &DagGraph, processors: u16) -> Option<u64> {
    if processors == 0 {
        return None;
    }
    let mut remaining_preds: Vec<usize> = (0..graph.len()).map(|v| graph.in_degree(v)).collect();
    let mut ready: alloc::collections::BTreeSet<usize> = (0..graph.len())
        .filter(|&v| remaining_preds[v] == 0)
        .collect();
    let mut running: Vec<(u64, usize)> = Vec::new(); // (finish time, node)
    let mut free = processors as usize;
    let mut now = 0u64;
    let mut finished = 0usize;

    loop {
        while free > 0 {
            let Some(v) = ready.pop_first() else { break };
            running.push((now + graph.wcet(v), v));
            free -= 1;
        }
        let Some(next) = running.iter().map(|&(f, _)| f).min() else {
            break;
        };
        now = next;
        let mut i = 0;
        while i < running.len() {
            if running[i].0 == now {
                let (_, v) = running.swap_remove(i);
                finished += 1;
                free += 1;
                for &s in graph.successors(v) {
                    remaining_preds[s] -= 1;
                    if remaining_preds[s] == 0 {
                        ready.insert(s);
                    }
                }
            } else {
                i += 1;
            }
        }
    }

    (finished == graph.len()).then_some(now)
}

/// Which published federated-scheduling algorithm decides admission. Each
/// is defined for one class of task system, so [`Self::for_task_set`]
/// picks the one matching the task set's deadlines.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FederatedVariant {
    /// Li, Chen, Agrawal, Lu, Gill, Saifullah, "Analysis of federated and
    /// global scheduling for parallel real-time tasks", ECRTS 2014 --
    /// implicit deadlines (`D = T`). High-utilization tasks (`U_i >= 1`)
    /// get `n_i = ceil((C_i - L_i)/(D_i - L_i))` dedicated processors; the
    /// low-utilization tasks are admitted iff `m_low >= 2 * Σ U_low` on the
    /// `m_low` processors left (Theorem 5.1 as restated in the Verucchi et
    /// al. 2023 survey), then placed first-fit for run time.
    LiImplicit,
    /// Baruah, "The federated scheduling of constrained-deadline sporadic
    /// DAG task systems", DATE 2015 (`FEDCONS`) -- constrained deadlines
    /// (`D <= T`). `MINPROCS` = smallest `μ >= ceil(δ_i)` for which list
    /// scheduling meets `D_i` (Fig. 3); low-density tasks by `PARTITION`
    /// (Fig. 4: deadline-ordered first-fit, DBF* test).
    BaruahConstrained,
    /// Baruah, "Federated scheduling of sporadic DAG task systems", IPDPS
    /// 2015 (`FEDERATED`) -- arbitrary deadlines. `MINPROCS` (Fig. 3) is list
    /// scheduling for `D <= T` and Lemma 1's Condition 1 for `D > T`;
    /// `PARTITION` (Fig. 4) adds the utilization condition.
    BaruahArbitrary,
}

impl FederatedVariant {
    /// Every `D = T` -> [`Self::LiImplicit`]; else every `D <= T` ->
    /// [`Self::BaruahConstrained`]; else [`Self::BaruahArbitrary`].
    pub fn for_task_set<'a>(configs: impl IntoIterator<Item = &'a DagMetrics>) -> Self {
        let mut all_implicit = true;
        let mut all_constrained = true;
        for c in configs {
            all_implicit &= c.relative_deadline == c.period;
            all_constrained &= c.relative_deadline <= c.period;
        }
        if all_implicit {
            FederatedVariant::LiImplicit
        } else if all_constrained {
            FederatedVariant::BaruahConstrained
        } else {
            FederatedVariant::BaruahArbitrary
        }
    }
}

/// One DAG as the batch admission sees it: its metrics plus, for
/// list scheduling, its precedence structure.
#[derive(Debug, Clone, Copy)]
pub struct FedTask<'a> {
    pub metrics: DagMetrics,
    pub graph: &'a DagGraph,
}

/// Where one DAG of a batch goes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FedPlan {
    /// High-density: `cores` processors for its exclusive use.
    Heavy { cores: u16 },
    /// Low-density: partitioned onto shared processor `processor` (an index
    /// among the batch's shared processors, not a cpu id).
    Light { processor: usize },
}

/// The whole batch decision, in the input's order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FederatedBatchPlan {
    pub variant: FederatedVariant,
    pub plans: Vec<FedPlan>,
    /// `Σ m_i` over the high-density tasks.
    pub heavy_cores: u16,
}

/// `δ_i >= 1` with `δ_i = vol_i / min(D_i, T_i)` -- Baruah's high-density
/// test (DATE/IPDPS 2015 Sec. II). For [`FederatedVariant::LiImplicit`]
/// (`D = T`) this is Li et al.'s high-utilization test `u_i >= 1`, using
/// the `>= 1` boundary as Baruah restates Li et al.'s terminology; a task
/// with exactly `u_i = 1` needs one whole processor either way.
fn is_high_density(c: &DagMetrics) -> bool {
    c.volume >= density_window(c)
}

/// `MINPROCS(τ_i, m_r)` for `variant`: the number of processors to dedicate
/// to high-density `task`, or `None` if it needs more than `m_r` (the
/// papers' `∞`).
fn min_procs(variant: FederatedVariant, task: &FedTask<'_>, m_r: u16) -> Option<u16> {
    let c = &task.metrics;
    let (vol, len, d, t) = (c.volume, c.critical_path, c.relative_deadline, c.period);
    if len > d {
        return None;
    }

    if variant == FederatedVariant::LiImplicit {
        // Li et al.: n_i = ceil((C_i - L_i) / (D_i - L_i)).
        let n = if d == len {
            // No slack at all: only a purely sequential DAG (C = L) fits,
            // on one processor.
            (vol == len).then_some(1u64)?
        } else {
            (vol - len).div_ceil(d - len).max(1)
        };
        return u16::try_from(n).ok().filter(|&n| n <= m_r);
    }

    // Baruah (Fig. 3): for μ <- ceil(δ_i) to m_r.
    let first = vol.div_ceil(density_window(c)).max(1);
    let first = u16::try_from(first).ok()?;
    if d <= t {
        // Lines 2-4: list scheduling makespan <= D_i.
        (first..=m_r).find(|&mu| list_schedule_makespan(task.graph, mu).is_some_and(|ms| ms <= d))
    } else {
        // Lines 7-8 (IPDPS only): Lemma 1's Condition 1,
        // (D div T)·vol + min(μ·(D mod T), vol) <= μ·D - (μ-1)·len.
        (first..=m_r).find(|&mu| {
            let mu = mu as i128;
            let (vol, len, d, t) = (vol as i128, len as i128, d as i128, t as i128);
            let lhs = (d / t) * vol + (mu * (d % t)).min(vol);
            let rhs = mu * d - (mu - 1) * len;
            lhs <= rhs
        })
    }
}

/// Decide `tasks` as one task system on `m` processors under `variant`
/// (`FEDERATED(τ, m)` / `FEDCONS(τ, m)`): every high-density task gets
/// `MINPROCS` processors (in input order, `m_r` shrinking as it goes;
/// `FAILURE` once one needs more than `m_r`), then every low-density task
/// is partitioned onto the `m_r` processors left. Pure -- no resource
/// ledger is touched.
pub fn plan_batch(
    tasks: &[FedTask<'_>],
    m: u16,
    variant: FederatedVariant,
) -> Result<FederatedBatchPlan, AdmissionError> {
    // The variant's preconditions (deadline model, `L <= D`, and for Li
    // `D > L` whenever there is parallel work), each DAG reported by its
    // position in `tasks`.
    precondition::check_all(Policy::Federated(variant), tasks.iter().map(|t| &t.metrics))?;

    let mut plans: Vec<Option<FedPlan>> = alloc::vec![None; tasks.len()];
    let mut m_r = m;

    for (i, task) in tasks.iter().enumerate() {
        let c = &task.metrics;
        if !is_high_density(c) {
            continue;
        }
        let m_i = min_procs(variant, task, m_r).ok_or(AdmissionError::NoFeasibleAllocation)?;
        m_r -= m_i;
        plans[i] = Some(FedPlan::Heavy { cores: m_i });
    }

    let light: Vec<usize> = (0..tasks.len()).filter(|&i| plans[i].is_none()).collect();
    let seq: Vec<SeqTask> = light
        .iter()
        .map(|&i| SeqTask {
            volume: tasks[i].metrics.volume,
            deadline: tasks[i].metrics.relative_deadline,
            period: tasks[i].metrics.period,
        })
        .collect();
    let condition = match variant {
        FederatedVariant::LiImplicit => {
            // Li et al. (ECRTS 2014) admit the low-utilization tasks by
            // total utilization alone, `m_low >= 2 * Σ_{low} U_x` (as
            // restated in Verucchi et al., RTS 2023, Theorem 5.1), and then
            // allow "any multiprocessor scheduling algorithm" for them.
            // That condition is the admission test here; the first-fit
            // partition below only picks the run-time placement, and with
            // every u_x < 1 it cannot fail once `Σ U <= m_low / 2` holds
            // (first-fit EDF succeeds whenever `Σ U <= (m_low + 1) / 2`,
            // López et al.'s bound for u_max <= 1).
            const EPS: f64 = 1e-9;
            let u_low: f64 = seq.iter().map(|t| t.volume as f64 / t.period as f64).sum();
            if 2.0 * u_low > m_r as f64 + EPS {
                return Err(AdmissionError::NoFeasibleAllocation);
            }
            Condition::Demand
        }
        FederatedVariant::BaruahConstrained => Condition::Demand,
        FederatedVariant::BaruahArbitrary => Condition::DemandAndUtilization,
    };
    let (placement, _) = partition::partition(&seq, m_r, condition, PackingStrategy::FirstFit)
        .ok_or(AdmissionError::NoFeasibleAllocation)?;
    for (&i, &processor) in light.iter().zip(placement.iter()) {
        plans[i] = Some(FedPlan::Light { processor });
    }

    Ok(FederatedBatchPlan {
        variant,
        plans: plans
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or(AdmissionError::NoFeasibleAllocation)?,
        heavy_cores: m - m_r,
    })
}

/// Pure yes/no: would `tasks` be accepted on `m` processors under the
/// variant matching its deadlines ([`FederatedVariant::for_task_set`])?
pub fn is_batch_feasible(tasks: &[FedTask<'_>], m: u16) -> bool {
    let variant = FederatedVariant::for_task_set(tasks.iter().map(|t| &t.metrics));
    plan_batch(tasks, m, variant).is_ok()
}

/// Admit `tasks` as one all-or-nothing batch against the cores currently
/// free in [`resource`], under the variant matching its deadlines. Only
/// once the whole plan fits are real cores claimed: one exclusive cluster
/// per high-density DAG, and one core per shared processor that received
/// at least one low-density DAG.
///
/// Run-time mapping: a high-density DAG runs EDF restricted to its own
/// cluster ([`SchedulerType::ClusteredEDF`]), a low-density DAG
/// uniprocessor EDF on its partition's single core (the same scheduler on a
/// one-core set). For Li et al. and for IPDPS 2015's `D > T` case that is
/// the papers' own run-time rule (any greedy scheduler / EDF). For
/// `D <= T` under Baruah's algorithms the papers instead replay the
/// list-scheduling template `σ_i` as a lookup table (DATE 2015 Sec. IV-A),
/// which this kernel does not implement -- the *admission* decision is
/// the paper's, the high-density dispatch is not.
///
/// Returns the variant used and one [`FederatedAssignment`] per input, in
/// order.
pub fn admit_batch(
    tasks: &[FedTask<'_>],
) -> Result<(FederatedVariant, Vec<FederatedAssignment>), AdmissionError> {
    let m = resource::free_core_count();
    let variant = FederatedVariant::for_task_set(tasks.iter().map(|t| &t.metrics));
    let plan = plan_batch(tasks, m, variant)?;

    let mut shared_cpus: Vec<Option<usize>> = Vec::new();
    let mut out = Vec::with_capacity(tasks.len());
    for (task, fed_plan) in tasks.iter().zip(plan.plans.iter()) {
        let c = &task.metrics;
        let (class, cores) = match *fed_plan {
            FedPlan::Heavy { cores } => (
                TaskClass::Heavy {
                    required_cores: cores,
                },
                resource::allocate_cluster(cores)?,
            ),
            FedPlan::Light { processor } => {
                if shared_cpus.len() <= processor {
                    shared_cpus.resize(processor + 1, None);
                }
                let cpu = match shared_cpus[processor] {
                    Some(cpu) => cpu,
                    None => {
                        let cpu = resource::allocate_cluster(1)?
                            .iter()
                            .next()
                            .ok_or(AdmissionError::NoFeasibleAllocation)?;
                        shared_cpus[processor] = Some(cpu);
                        cpu
                    }
                };
                (TaskClass::Light, CpuSet::empty().with(cpu))
            }
        };
        out.push(FederatedAssignment {
            class,
            scheduler_type: SchedulerType::ClusteredEDF(c.relative_deadline, cores),
            source: c.source,
        });
    }

    Ok((variant, out))
}

/// Paper-conformance tests: worked examples of Li et al. (ECRTS 2014) and
/// Baruah (DATE 2015, IPDPS 2015).
#[cfg(test)]
mod paper_examples;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dag::DagError;
    use crate::dag_sched::resource::ResourceError;

    #[test]
    fn test_is_heavy_boundary() {
        // u = C/T == 1 is Light (u <= 1), not Heavy.
        assert!(!is_heavy(100, 100));
        assert!(is_heavy(101, 100));
    }

    #[test]
    fn test_required_cores_formula() {
        // m = ceil((100 - 20) / (50 - 20)) = ceil(80 / 30) = 3
        let config = DagMetrics::from_static(100, 20, 1000, 50);
        assert_eq!(config.min_dedicated_cores(), Some(3));
    }

    #[test]
    fn test_required_cores_sequential_dag_clamped_to_one() {
        // A DAG with no exploitable parallelism (volume == critical_path)
        // still needs exactly one dedicated core.
        let config = DagMetrics::from_static(50, 50, 1000, 60);
        assert_eq!(config.min_dedicated_cores(), Some(1));
    }

    #[test]
    fn test_required_cores_infeasible_deadline() {
        assert_eq!(
            DagMetrics::from_static(100, 50, 1000, 50).min_dedicated_cores(),
            None
        ); // D <= L
        assert_eq!(
            DagMetrics::from_static(100, 50, 1000, 40).min_dedicated_cores(),
            None
        ); // D < L
    }

    #[test]
    fn test_classify_dag_infeasible_when_strictly_past_deadline() {
        // relative_deadline(40) < critical_path(50): infeasible regardless
        // of heaviness, since even the critical path alone can't finish.
        let config = DagMetrics::from_static(10, 50, 1000, 40);
        assert_eq!(
            classify_dag(&config),
            Err(AdmissionError::Precondition(
                DagError::CriticalPathExceedsDeadline {
                    dag_id: 0,
                    critical_path: 50,
                    relative_deadline: 40,
                }
            ))
        );
    }

    #[test]
    fn test_classify_dag_deadline_equals_critical_path_light_ok() {
        // relative_deadline == critical_path == volume: a purely sequential
        // DAG (no parallel-only work) fits its own critical path in exactly
        // D == L time on a single core -- feasible, not the unconditional
        // Infeasible case.
        let config = DagMetrics::from_static(50, 50, 1000, 50);
        assert_eq!(classify_dag(&config), Ok(TaskClass::Light));
    }

    #[test]
    fn test_classify_dag_deadline_equals_critical_path_heavy_infeasible() {
        // relative_deadline == critical_path but volume > critical_path:
        // there's parallel-only work left to fit in a now-zero slack
        // window, which no core count can do.
        let config = DagMetrics::from_static(100, 50, 1000, 50);
        assert_eq!(
            classify_dag(&config),
            Err(AdmissionError::Precondition(
                DagError::NoSlackForParallelWork {
                    dag_id: 0,
                    volume: 100,
                    critical_path: 50,
                }
            ))
        );
    }

    #[test]
    fn test_classify_dag_light() {
        // density_window = min(D=90, T=100) = 90; volume(80) <= 90 => Light
        let config = DagMetrics::from_static(80, 20, 100, 90);
        assert_eq!(classify_dag(&config), Ok(TaskClass::Light));
    }

    #[test]
    fn test_classify_dag_heavy() {
        // D == T (implicit deadline): density_window = 50; volume(100) > 50 => Heavy
        let config = DagMetrics::from_static(100, 20, 50, 50);
        assert_eq!(
            classify_dag(&config),
            Ok(TaskClass::Heavy { required_cores: 3 }) // ceil((100-20)/(50-20)) = 3
        );
    }

    #[test]
    fn test_classify_dag_constrained_deadline_reclassifies_as_heavy() {
        // volume(60) <= period(100) => Light under plain utilization u=C/T
        // (0.6), but relative_deadline(50) < period(100) makes this a
        // constrained-deadline DAG whose density_window is 50, not 100:
        // density = 60/50 = 1.2 > 1 => Heavy. A DAG this tight cannot
        // actually be spread thin over the shared light pool just because
        // its long-run utilization looks low.
        let config = DagMetrics::from_static(60, 10, 100, 50);
        assert_eq!(
            classify_dag(&config),
            Ok(TaskClass::Heavy { required_cores: 2 }) // ceil((60-10)/(50-10)) = 2
        );
    }

    #[test]
    fn test_classify_dag_from_measured_matches_from_static() {
        // The two constructors differ only in `source`; admission math must
        // be identical either way, since a human-entered estimate and an
        // rd_gen-computed value are interchangeable inputs to the same
        // classification.
        let static_config = DagMetrics::from_static(100, 20, 50, 50);
        let measured_config = DagMetrics::from_measured(100, 20, 50, 50);

        assert!(!static_config.is_measured());
        assert!(measured_config.is_measured());
        assert_eq!(classify_dag(&static_config), classify_dag(&measured_config));
    }

    // Exercises resource::allocate_cluster/release_cluster/admit_dag
    // together in one test: they share the process-global ledger in
    // `dag_sched::resource`, and `cargo test` runs tests in parallel
    // threads, so splitting this across multiple #[test] fns would risk
    // cross-test interference.
    #[test]
    fn test_cluster_allocation_lifecycle() {
        unsafe {
            // workers 1..10 (9); core 9 is the regular pool, so the DAG pool
            // (1..9) has 8 cores available — matching the "8 available"
            // comments below.
            awkernel_lib::cpu::set_num_cpu(10);
        }

        let heavy_a = resource::allocate_cluster(3).unwrap();
        let heavy_b = resource::allocate_cluster(3).unwrap();
        assert!(!heavy_a.contains(9) && !heavy_b.contains(9)); // never claims the regular-pool core
        assert_eq!(heavy_a.union(heavy_b).iter().count(), 6); // disjoint: 3 + 3 distinct cores
        for cpu in heavy_a.iter() {
            assert!(!heavy_b.contains(cpu));
        }

        // Only 2 workers remain (8 - 3 - 3); a third 3-core cluster must fail.
        match resource::allocate_cluster(3) {
            Err(ResourceError::InsufficientCores {
                required: 3,
                available: 2,
            }) => {}
            other => {
                panic!("expected InsufficientCores{{required: 3, available: 2}}, got {other:?}")
            }
        }

        resource::release_cluster(heavy_a);
        let heavy_c = resource::allocate_cluster(3).unwrap();
        assert!(heavy_c.iter().all(|cpu| !heavy_b.contains(cpu)));

        // admit_dag end-to-end: Light gets GEDF, Heavy gets a fresh cluster.
        // density_window = min(D=50, T=100) = 50, so admit_dag reserves
        // utilization against 50, not 100 — release must match.
        let light = admit_dag(DagMetrics::from_static(10, 5, 100, 50)).unwrap();
        assert_eq!(light.class, TaskClass::Light);
        assert_eq!(light.source, MetricsSource::Static);
        assert!(matches!(light.scheduler_type, SchedulerType::GEDF(50)));
        resource::release_light_utilization(10, 50); // undo admit_dag's reservation before the next scenario

        resource::release_cluster(heavy_b);
        resource::release_cluster(heavy_c);

        // Light-pool oversubscription: claim 7 of the 8 workers for a heavy
        // cluster, leaving exactly 1 core (100% = 1_000_000 scaled) for the
        // light pool.
        let heavy_big = resource::allocate_cluster(7).unwrap();

        resource::reserve_light_utilization(60, 100).unwrap(); // u = 0.6, committed = 600_000

        match resource::reserve_light_utilization(50, 100) {
            // u = 0.5 => additional 500_000; 600_000 + 500_000 > 1_000_000
            Err(ResourceError::LightPoolOversubscribed {
                additional_utilization_scaled: 500_000,
                available_capacity_scaled: 400_000,
            }) => {}
            other => panic!(
                "expected LightPoolOversubscribed{{additional: 500_000, available: 400_000}}, got {other:?}"
            ),
        }

        resource::release_light_utilization(60, 100); // frees the 600_000 back up

        // Now the same 0.5-utilization DAG fits, this time via a
        // human-supplied estimate rather than a static rd_gen value.
        let heavy_config = DagMetrics::from_measured(50, 10, 100, 90);
        assert!(matches!(
            classify_dag(&heavy_config).unwrap(),
            TaskClass::Light
        ));
        resource::reserve_light_utilization(50, 100).unwrap();
        resource::release_light_utilization(50, 100);

        resource::release_cluster(heavy_big);
    }

    // ----- batch admission (Li / DATE 2015 / IPDPS 2015) -----

    fn chain(wcets: &[u64]) -> DagGraph {
        let edges: Vec<(usize, usize)> = (1..wcets.len()).map(|i| (i - 1, i)).collect();
        DagGraph::new(wcets.to_vec(), &edges).unwrap()
    }

    /// `k` independent nodes of WCET `w` (a fully parallel DAG).
    fn parallel(k: usize, w: u64) -> DagGraph {
        DagGraph::new(alloc::vec![w; k], &[]).unwrap()
    }

    #[test]
    fn test_list_schedule_makespan_rejects_zero_processors() {
        assert_eq!(list_schedule_makespan(&chain(&[1, 2]), 0), None);
    }

    #[test]
    fn test_list_schedule_makespan_rejects_cycle() {
        let g = DagGraph::new(alloc::vec![1, 1], &[(0, 1), (1, 0)]).unwrap();
        assert_eq!(list_schedule_makespan(&g, 2), None);
    }

    #[test]
    fn test_variant_for_task_set() {
        let implicit = DagMetrics::from_static(10, 5, 20, 20);
        let constrained = DagMetrics::from_static(10, 5, 20, 15);
        let arbitrary = DagMetrics::from_static(10, 5, 20, 30);
        assert_eq!(
            FederatedVariant::for_task_set([&implicit, &implicit]),
            FederatedVariant::LiImplicit
        );
        assert_eq!(
            FederatedVariant::for_task_set([&implicit, &constrained]),
            FederatedVariant::BaruahConstrained
        );
        assert_eq!(
            FederatedVariant::for_task_set([&constrained, &arbitrary]),
            FederatedVariant::BaruahArbitrary
        );
    }

    #[test]
    fn test_li_uses_closed_form_core_count() {
        // C=100, L=20, D=T=50: n = ceil(80/30) = 3.
        let g = parallel(1, 1); // structure unused by Li et al.
        let task = FedTask {
            metrics: DagMetrics::from_static(100, 20, 50, 50),
            graph: &g,
        };
        assert_eq!(min_procs(FederatedVariant::LiImplicit, &task, 16), Some(3));
        assert_eq!(min_procs(FederatedVariant::LiImplicit, &task, 2), None);
    }

    #[test]
    fn test_baruah_constrained_minprocs_is_list_scheduling() {
        // 4 parallel nodes of 10, D = 20 <= T = 100: δ = 40/20 = 2, and LS
        // on 2 processors finishes at 20 <= D, so μ = 2 -- where Li's
        // closed form would give ceil((40-10)/(20-10)) = 3.
        let g = parallel(4, 10);
        let task = FedTask {
            metrics: DagMetrics::from_static(40, 10, 100, 20),
            graph: &g,
        };
        assert_eq!(
            min_procs(FederatedVariant::BaruahConstrained, &task, 16),
            Some(2)
        );
        assert_eq!(
            min_procs(FederatedVariant::BaruahConstrained, &task, 1),
            None
        );
    }

    #[test]
    fn test_baruah_arbitrary_condition1() {
        // D=25 > T=10, vol=30, len=5, δ = 30/10 = 3.
        // μ=3: 2·30 + min(3·5, 30) = 75 > 3·25 - 2·5 = 65.
        // μ=4: 2·30 + min(4·5, 30) = 80 <= 4·25 - 3·5 = 85.
        let g = chain(&[5]);
        let task = FedTask {
            metrics: DagMetrics::from_static(30, 5, 10, 25),
            graph: &g,
        };
        assert_eq!(
            min_procs(FederatedVariant::BaruahArbitrary, &task, 16),
            Some(4)
        );
        assert_eq!(min_procs(FederatedVariant::BaruahArbitrary, &task, 3), None);
    }

    #[test]
    fn test_plan_batch_partitions_low_density_tasks() {
        let g = chain(&[3]);
        // Three low-density implicit tasks, u = 0.3, 0.4, 0.5: first-fit
        // puts 0.3+0.4 on processor 0 and 0.5 on processor 1.
        let tasks: Vec<FedTask<'_>> = [3u64, 4, 5]
            .iter()
            .map(|&c| FedTask {
                metrics: DagMetrics::from_static(c, 1, 10, 10),
                graph: &g,
            })
            .collect();
        let plan = plan_batch(&tasks, 2, FederatedVariant::BaruahConstrained).unwrap();
        assert_eq!(
            plan.plans,
            alloc::vec![
                FedPlan::Light { processor: 0 },
                FedPlan::Light { processor: 0 },
                FedPlan::Light { processor: 1 },
            ]
        );
        assert!(plan_batch(&tasks, 1, FederatedVariant::BaruahConstrained).is_err());
    }

    #[test]
    fn test_li_admits_low_utilization_tasks_by_twice_total_utilization() {
        // Same three tasks, Σ U = 1.2: a first-fit partition fits them on 2
        // processors, but Li et al.'s condition needs m_low >= 2 * 1.2 = 2.4.
        let g = chain(&[3]);
        let tasks: Vec<FedTask<'_>> = [3u64, 4, 5]
            .iter()
            .map(|&c| FedTask {
                metrics: DagMetrics::from_static(c, 1, 10, 10),
                graph: &g,
            })
            .collect();
        assert!(plan_batch(&tasks, 2, FederatedVariant::LiImplicit).is_err());
        assert!(plan_batch(&tasks, 3, FederatedVariant::LiImplicit).is_ok());
    }

    #[test]
    fn test_plan_batch_heavy_then_light_on_remaining() {
        let heavy_g = parallel(4, 10);
        let light_g = chain(&[5]);
        let tasks = [
            FedTask {
                metrics: DagMetrics::from_static(40, 10, 100, 20), // μ = 2
                graph: &heavy_g,
            },
            FedTask {
                metrics: DagMetrics::from_static(5, 5, 100, 50),
                graph: &light_g,
            },
        ];
        let plan = plan_batch(&tasks, 3, FederatedVariant::BaruahConstrained).unwrap();
        assert_eq!(plan.plans[0], FedPlan::Heavy { cores: 2 });
        assert_eq!(plan.plans[1], FedPlan::Light { processor: 0 });
        assert_eq!(plan.heavy_cores, 2);
        // Only 2 processors: the heavy task takes both, nothing left.
        assert!(plan_batch(&tasks, 2, FederatedVariant::BaruahConstrained).is_err());
    }

    #[test]
    fn test_plan_batch_rejects_variant_outside_its_deadline_class() {
        let g = chain(&[5]);
        let constrained = [FedTask {
            metrics: DagMetrics::from_static(5, 5, 100, 50),
            graph: &g,
        }];
        let arbitrary = [FedTask {
            metrics: DagMetrics::from_static(5, 5, 100, 150),
            graph: &g,
        }];
        assert_eq!(
            plan_batch(&constrained, 4, FederatedVariant::LiImplicit),
            Err(AdmissionError::Precondition(
                DagError::ImplicitDeadlineRequired {
                    dag_id: 0,
                    relative_deadline: 50,
                    period: 100,
                }
            ))
        );
        assert_eq!(
            plan_batch(&arbitrary, 4, FederatedVariant::BaruahConstrained),
            Err(AdmissionError::Precondition(
                DagError::ConstrainedDeadlineRequired {
                    dag_id: 0,
                    relative_deadline: 150,
                    period: 100,
                }
            ))
        );
        assert!(plan_batch(&arbitrary, 4, FederatedVariant::BaruahArbitrary).is_ok());
    }

    #[test]
    fn test_plan_batch_rejects_critical_path_past_deadline() {
        let g = chain(&[30]);
        let tasks = [FedTask {
            metrics: DagMetrics::from_static(30, 30, 100, 20),
            graph: &g,
        }];
        assert_eq!(
            plan_batch(&tasks, 4, FederatedVariant::BaruahConstrained),
            Err(AdmissionError::Precondition(
                DagError::CriticalPathExceedsDeadline {
                    dag_id: 0,
                    critical_path: 30,
                    relative_deadline: 20,
                }
            ))
        );
    }
}
