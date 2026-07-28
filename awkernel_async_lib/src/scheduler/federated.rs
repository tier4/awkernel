//! Federated Scheduling admission layer (Li et al., RTSS 2014) for DAG tasks.
//!
//! Federated Scheduling classifies a DAG by utilization `u = C/T`:
//! - **Heavy** (`u > 1`): given an exclusive cluster of `m` cores.
//! - **Light** (`u <= 1`): shares the remaining cores with other light DAGs,
//!   admitted only while the sum of every admitted light DAG's utilization
//!   still fits the pool (see [`reserve_light_utilization`]) — a heavy DAG's
//!   theorem-backed core count is worthless if the light side is silently
//!   oversubscribed instead.
//!
//! This module is admission-time only. It does not add a new run queue or a
//! new [`super::Scheduler`] impl: [`SchedulerType::ClusteredEDF`] already
//! implements "EDF restricted to a `CpuSet`" (cluster reservation via
//! `NUM_CLUSTERED_TASKS_ALIVE`, preemption, the lot), so a heavy DAG's
//! cluster is simply a `ClusteredEDF` cpu_set computed here; a light DAG uses
//! plain [`SchedulerType::GEDF`]. Both already compute one shared
//! per-instance absolute deadline for every node of a DAG via
//! [`super::gedf::calculate_and_update_dag_deadline`], so this module does
//! not duplicate that logic — it only decides *which* scheduler and *which*
//! cores.
//!
//! [`admit_dag`] is the single entry point, taking one [`DagAdmissionConfig`].
//! That config is deliberately the *only* thing admission looks at, so a
//! caller with a fully-known static DAG structure (e.g. `rd_gen_to_dags`,
//! via [`DagAdmissionConfig::from_static`]) and a caller who can only supply
//! a human estimate for a dynamically-built DAG (via
//! [`DagAdmissionConfig::from_measured`]) go through the exact same
//! admission logic — neither path is a special case of the other.

use awkernel_lib::{
    cpu::{num_cpu, CpuSet},
    sync::mutex::{MCSNode, Mutex},
};

use alloc::vec::Vec;

use super::SchedulerType;

/// Where a [`DagAdmissionConfig`]'s `volume`/`critical_path` came from.
///
/// Never affects the admission math — [`classify_dag`] reads the same four
/// numbers either way — it only records provenance, e.g. so a caller can
/// avoid presenting a `Static` (`rd_gen`-sourced) `L` as if it still meant
/// something after admission, when in fact it never does again ([`Static`]'s
/// only job is being an input to this module).
///
/// [`Static`]: MetricsSource::Static
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetricsSource {
    /// Computed ahead of time from a fully-known static DAG structure, e.g.
    /// a topological-sort DP over per-node WCET declared in an `rd_gen`
    /// YAML file (see `rd_gen_to_dags::dag_stats::compute_dag_stats`).
    Static,
    /// A human's own estimate today; once a live-measurement source exists
    /// for DAGs whose structure isn't known ahead of admission, that would
    /// also produce this variant.
    Measured,
}

/// Everything [`admit_dag`] needs to decide a DAG's `SchedulerType`, gathered
/// into one config. Build it with [`DagAdmissionConfig::from_static`] (a
/// priori known structure) or [`DagAdmissionConfig::from_measured`] (a
/// human-supplied estimate); both produce the identical type, so admission
/// itself never has to know which path a value took to get here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DagAdmissionConfig {
    /// `C`: total WCET volume, i.e. the sum of every node's WCET.
    pub volume: u64,
    /// `L`: critical-path length, i.e. the WCET sum along the longest
    /// source-to-sink path. Only ever consulted during admission (here); it
    /// has no meaning afterwards.
    pub critical_path: u64,
    /// `T`: period. Drives heavy/light classification (`u = C/T`).
    pub period: u64,
    /// `D`: relative deadline. Drives the heavy-cluster core count and is
    /// handed to the resulting `SchedulerType`, which computes the actual
    /// per-instance *absolute* deadline itself (`wake_time + D`, shared
    /// across every node of one DAG instance) the first time it is needed —
    /// this config only carries the relative quantity.
    ///
    /// In the same time unit as `volume`/`critical_path`/`period`, and as
    /// [`SchedulerType::GEDF`]/[`SchedulerType::ClusteredEDF`]'s own
    /// `relative_deadline` parameter (this crate's scheduler layer treats it
    /// as an opaque `u64`; callers must stay consistent, exactly as those
    /// two variants already require).
    pub relative_deadline: u64,
    pub source: MetricsSource,
}

impl DagAdmissionConfig {
    /// Build a config from a priori-known values, e.g. rd_gen_to_dags's
    /// `compute_dag_stats` over a YAML-declared DAG structure.
    pub const fn from_static(
        volume: u64,
        critical_path: u64,
        period: u64,
        relative_deadline: u64,
    ) -> Self {
        Self {
            volume,
            critical_path,
            period,
            relative_deadline,
            source: MetricsSource::Static,
        }
    }

    /// Build a config from a human-supplied estimate (today) or a future
    /// live measurement (once that infrastructure exists), for a DAG whose
    /// full structure isn't known ahead of admission.
    pub const fn from_measured(
        volume: u64,
        critical_path: u64,
        period: u64,
        relative_deadline: u64,
    ) -> Self {
        Self {
            volume,
            critical_path,
            period,
            relative_deadline,
            source: MetricsSource::Measured,
        }
    }

    pub const fn is_measured(&self) -> bool {
        matches!(self.source, MetricsSource::Measured)
    }
}

/// Result of [`classify_dag`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskClass {
    Light,
    Heavy { required_cores: u16 },
}

/// The `SchedulerType` (and, for heavy DAGs, the allocated cluster) that
/// [`admit_dag`] decided a DAG's nodes should use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FederatedAssignment {
    pub class: TaskClass,
    pub scheduler_type: SchedulerType,
    /// Carried over from the [`DagAdmissionConfig`] that produced this
    /// assignment, so a caller can log/display it without keeping the
    /// original config around.
    pub source: MetricsSource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FederatedError {
    /// `relative_deadline <= critical_path`: no core count can meet this
    /// deadline, since traversing the critical path alone already takes at
    /// least `critical_path`.
    Infeasible {
        critical_path: u64,
        relative_deadline: u64,
    },
    /// A heavy DAG needs `required` dedicated cores but fewer than that are
    /// currently free.
    InsufficientCores { required: u16, available: u16 },
    /// A light DAG's own utilization would push the shared light pool's
    /// committed total over its capacity (see [`reserve_light_utilization`]).
    /// Both fields are scaled by [`UTILIZATION_SCALE`].
    LightPoolOversubscribed {
        additional_utilization_scaled: u64,
        available_capacity_scaled: u64,
    },
}

impl core::fmt::Display for FederatedError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FederatedError::Infeasible {
                critical_path,
                relative_deadline,
            } => write!(
                f,
                "relative_deadline({relative_deadline}) <= critical_path({critical_path}); no core count can meet this deadline"
            ),
            FederatedError::InsufficientCores {
                required,
                available,
            } => write!(
                f,
                "heavy DAG needs {required} dedicated core(s) but only {available} are free"
            ),
            FederatedError::LightPoolOversubscribed {
                additional_utilization_scaled,
                available_capacity_scaled,
            } => write!(
                f,
                "light pool oversubscribed: this DAG needs {}.{:02}% more utilization but only {}.{:02}% is free",
                additional_utilization_scaled / 10_000,
                (additional_utilization_scaled % 10_000) / 100,
                available_capacity_scaled / 10_000,
                (available_capacity_scaled % 10_000) / 100,
            ),
        }
    }
}

/// `u = C/T`: a DAG is heavy iff its WCET volume exceeds its period.
const fn is_heavy(volume: u64, period: u64) -> bool {
    volume > period
}

/// `m = ceil((C - L) / (D - L))`, clamped to at least 1: a DAG whose volume
/// equals its critical path has no exploitable parallelism, but still needs
/// one dedicated core to run on. Returns `None` if `D <= L` (infeasible,
/// checked by the caller before this runs) or if the result does not fit a
/// `u16` (unreachable in practice: bounded by `NUM_MAX_CPU`).
fn required_cores(volume: u64, critical_path: u64, relative_deadline: u64) -> Option<u16> {
    let numerator = volume.checked_sub(critical_path)?;
    let denominator = relative_deadline.checked_sub(critical_path)?;
    if denominator == 0 {
        return None;
    }
    let cores = numerator.div_ceil(denominator).max(1);
    u16::try_from(cores).ok()
}

/// Classify a DAG and, if heavy, compute its required core count. Does not
/// allocate any cores; see [`allocate_cluster`] / [`admit_dag`] for that.
pub fn classify_dag(config: &DagAdmissionConfig) -> Result<TaskClass, FederatedError> {
    if config.relative_deadline <= config.critical_path {
        return Err(FederatedError::Infeasible {
            critical_path: config.critical_path,
            relative_deadline: config.relative_deadline,
        });
    }

    if !is_heavy(config.volume, config.period) {
        return Ok(TaskClass::Light);
    }

    let Some(required_cores) =
        required_cores(config.volume, config.critical_path, config.relative_deadline)
    else {
        return Err(FederatedError::Infeasible {
            critical_path: config.critical_path,
            relative_deadline: config.relative_deadline,
        });
    };

    Ok(TaskClass::Heavy { required_cores })
}

/// Utilization is tracked as an integer scaled by this factor (parts per
/// million) rather than a float, so the light-pool admission check below
/// stays exact and panic-free. `u = 1.0` (100%) is represented as
/// `1_000_000`.
const UTILIZATION_SCALE: u64 = 1_000_000;

fn utilization_scaled(volume: u64, period: u64) -> u64 {
    // `volume`/`period` are WCET sums/periods in the caller's time unit,
    // orders of magnitude below `u64::MAX / UTILIZATION_SCALE` for any DAG
    // anyone would actually declare, so this cannot overflow in practice.
    // `period.max(1)` guards the degenerate `period == 0` input: such a DAG
    // is already classified Heavy by `is_heavy` (volume > 0 == 0 is false
    // only when volume is also 0, in which case this correctly yields 0),
    // so this path is only reachable for genuinely zero-utilization DAGs.
    volume.saturating_mul(UTILIZATION_SCALE) / period.max(1)
}

/// Whether the DAG pool / regular pool split (see [`is_dag_pool_core`] /
/// [`is_regular_pool_core`]) is in effect. Splitting off one core needs at
/// least 2 worker cores to leave anything for the DAG side, so systems with
/// only 1 worker (`num_cpu() < 3`) fall back to every worker being eligible
/// for both — i.e. today's shared-pool behavior, not a broken one.
pub(crate) fn dag_pool_split_active() -> bool {
    num_cpu() >= 3
}

/// True if `cpu_id` may run light-DAG (GEDF) work.
///
/// The last worker core is carved out for regular (non-DAG) tasks — the
/// shell, driver services, and the like — so a Federated-light DAG task is
/// never delayed by interference the admission math (`u = C/T`,
/// [`reserve_light_utilization`]) has no way to account for: none of that
/// analysis models shell/service load, only DAG-to-DAG contention. See
/// [`super::get_next_task`] for where this gates dispatch, and
/// [`super::gedf::calculate_and_update_dag_deadline`]'s callers for where it
/// gates preemption targets.
pub(crate) fn is_dag_pool_core(cpu_id: usize) -> bool {
    cpu_id != 0 && (!dag_pool_split_active() || cpu_id != num_cpu() - 1)
}

/// True if `cpu_id` may run regular (non-DAG) work: the complement of
/// [`is_dag_pool_core`] among worker cores while the split is active, and
/// (like it) true everywhere while the split is inactive.
pub(crate) fn is_regular_pool_core(cpu_id: usize) -> bool {
    cpu_id != 0 && (!dag_pool_split_active() || cpu_id == num_cpu() - 1)
}

/// Shared state for the Federated admission layer, bundled behind one lock
/// so a heavy admission (which shrinks the light pool) and a light
/// admission (which checks against it) can never interleave inconsistently.
struct FederatedPool {
    /// Cores currently claimed by some heavy DAG's exclusive cluster.
    /// Disjoint from (and unrelated to) `NUM_CLUSTERED_TASKS_ALIVE`: that
    /// counter tracks live *tasks* per CPU once spawned, while this tracks
    /// which worker CPUs this module has already promised to a cluster, so
    /// two heavy DAGs never get the same core.
    claimed_cores: CpuSet,
    /// Sum of every admitted light DAG's `u = C/T`, scaled by
    /// [`UTILIZATION_SCALE`].
    light_utilization_scaled: u64,
}

static POOL: Mutex<FederatedPool> = Mutex::new(FederatedPool {
    claimed_cores: CpuSet::empty(),
    light_utilization_scaled: 0,
});

/// DAG-pool worker CPUs not currently claimed by any heavy cluster — i.e.
/// the cores the light pool has to share. Excludes the regular-pool core
/// (see [`is_dag_pool_core`]), so it is never counted as light-pool
/// capacity nor handed out to a heavy cluster.
fn light_pool_size(pool: &FederatedPool) -> usize {
    (1..num_cpu())
        .filter(|&cpu| is_dag_pool_core(cpu) && !pool.claimed_cores.contains(cpu))
        .count()
}

/// Claim `required_cores` DAG-pool worker CPUs (`1..num_cpu()`, excluding
/// CPU 0 and the regular-pool core; see [`is_dag_pool_core`]) not already
/// claimed by another heavy cluster.
pub fn allocate_cluster(required_cores: u16) -> Result<CpuSet, FederatedError> {
    let required = required_cores as usize;

    let mut node = MCSNode::new();
    let mut pool = POOL.lock(&mut node);

    let free_workers: Vec<usize> = (1..num_cpu())
        .filter(|&cpu| is_dag_pool_core(cpu) && !pool.claimed_cores.contains(cpu))
        .collect();

    if free_workers.len() < required {
        return Err(FederatedError::InsufficientCores {
            required: required_cores,
            available: free_workers.len() as u16, // free_workers.len() < num_cpu() <= NUM_MAX_CPU (512), fits u16
        });
    }

    let mut cluster = CpuSet::empty();
    for cpu in free_workers.into_iter().take(required) {
        cluster.insert(cpu);
    }

    pool.claimed_cores = pool.claimed_cores.union(cluster);
    Ok(cluster)
}

/// Release a cluster previously returned by [`allocate_cluster`], making its
/// cores available to the next heavy DAG admitted.
pub fn release_cluster(cluster: CpuSet) {
    let mut node = MCSNode::new();
    let mut pool = POOL.lock(&mut node);
    for cpu in cluster.iter() {
        pool.claimed_cores.remove(cpu);
    }
}

/// Commit `volume/period`'s utilization against the shared light pool.
///
/// This is the necessary condition every scheduling algorithm requires
/// (`Σ light utilization <= light pool core count`); it is not by itself a
/// sufficient schedulability proof for any particular global scheduler, but
/// admitting past it is certain to be unschedulable, so it is enforced as a
/// hard gate.
pub fn reserve_light_utilization(volume: u64, period: u64) -> Result<(), FederatedError> {
    let additional = utilization_scaled(volume, period);

    let mut node = MCSNode::new();
    let mut pool = POOL.lock(&mut node);

    let capacity = (light_pool_size(&pool) as u64).saturating_mul(UTILIZATION_SCALE);
    let committed = pool.light_utilization_scaled;

    if committed.saturating_add(additional) > capacity {
        return Err(FederatedError::LightPoolOversubscribed {
            additional_utilization_scaled: additional,
            available_capacity_scaled: capacity.saturating_sub(committed),
        });
    }

    pool.light_utilization_scaled = committed + additional;
    Ok(())
}

/// Release utilization previously committed by [`reserve_light_utilization`].
pub fn release_light_utilization(volume: u64, period: u64) {
    let released = utilization_scaled(volume, period);
    let mut node = MCSNode::new();
    let mut pool = POOL.lock(&mut node);
    pool.light_utilization_scaled = pool.light_utilization_scaled.saturating_sub(released);
}

/// Admit a DAG: classify it and decide the `SchedulerType` every one of its
/// nodes should be registered with. Works identically whether `config` was
/// built via [`DagAdmissionConfig::from_static`] or
/// [`DagAdmissionConfig::from_measured`].
///
/// - Heavy: allocates its exclusive cluster (release it with
///   [`release_cluster`] once the DAG is torn down, if ever — none of this
///   test bed's DAGs currently are).
/// - Light: commits its utilization against the shared pool (release it with
///   [`release_light_utilization`] likewise).
pub fn admit_dag(config: DagAdmissionConfig) -> Result<FederatedAssignment, FederatedError> {
    match classify_dag(&config)? {
        TaskClass::Light => {
            reserve_light_utilization(config.volume, config.period)?;
            Ok(FederatedAssignment {
                class: TaskClass::Light,
                scheduler_type: SchedulerType::GEDF(config.relative_deadline),
                source: config.source,
            })
        }
        TaskClass::Heavy { required_cores } => {
            let cluster = allocate_cluster(required_cores)?;
            Ok(FederatedAssignment {
                class: TaskClass::Heavy { required_cores },
                scheduler_type: SchedulerType::ClusteredEDF(config.relative_deadline, cluster),
                source: config.source,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_heavy_boundary() {
        // u = C/T == 1 is Light (u <= 1), not Heavy.
        assert!(!is_heavy(100, 100));
        assert!(is_heavy(101, 100));
    }

    #[test]
    fn test_required_cores_formula() {
        // m = ceil((100 - 20) / (50 - 20)) = ceil(80 / 30) = 3
        assert_eq!(required_cores(100, 20, 50), Some(3));
    }

    #[test]
    fn test_required_cores_sequential_dag_clamped_to_one() {
        // A DAG with no exploitable parallelism (volume == critical_path)
        // still needs exactly one dedicated core.
        assert_eq!(required_cores(50, 50, 60), Some(1));
    }

    #[test]
    fn test_required_cores_infeasible_deadline() {
        assert_eq!(required_cores(100, 50, 50), None); // D <= L
        assert_eq!(required_cores(100, 50, 40), None); // D < L
    }

    #[test]
    fn test_classify_dag_infeasible_regardless_of_heaviness() {
        let config = DagAdmissionConfig::from_static(10, 50, 1000, 50); // relative_deadline == critical_path
        assert_eq!(
            classify_dag(&config),
            Err(FederatedError::Infeasible {
                critical_path: 50,
                relative_deadline: 50,
            })
        );
    }

    #[test]
    fn test_classify_dag_light() {
        // volume(80) <= period(100) => Light
        let config = DagAdmissionConfig::from_static(80, 20, 100, 90);
        assert_eq!(classify_dag(&config), Ok(TaskClass::Light));
    }

    #[test]
    fn test_classify_dag_heavy() {
        // volume(100) > period(50) => Heavy
        let config = DagAdmissionConfig::from_static(100, 20, 50, 50);
        assert_eq!(
            classify_dag(&config),
            Ok(TaskClass::Heavy { required_cores: 3 }) // ceil((100-20)/(50-20)) = 3
        );
    }

    #[test]
    fn test_classify_dag_from_measured_matches_from_static() {
        // The two constructors differ only in `source`; admission math must
        // be identical either way, since a human-entered estimate and an
        // rd_gen-computed value are interchangeable inputs to the same
        // classification.
        let static_config = DagAdmissionConfig::from_static(100, 20, 50, 50);
        let measured_config = DagAdmissionConfig::from_measured(100, 20, 50, 50);

        assert!(!static_config.is_measured());
        assert!(measured_config.is_measured());
        assert_eq!(
            classify_dag(&static_config),
            classify_dag(&measured_config)
        );
    }

    #[test]
    fn test_dag_pool_split() {
        unsafe {
            awkernel_lib::cpu::set_num_cpu(10); // workers 1..10; last (9) is the regular-pool core
        }
        assert!(dag_pool_split_active());
        assert!(is_regular_pool_core(9));
        assert!(!is_dag_pool_core(9));
        for cpu in 1..9 {
            assert!(is_dag_pool_core(cpu), "cpu {cpu} should be in the DAG pool");
            assert!(!is_regular_pool_core(cpu), "cpu {cpu} should not be the regular-pool core");
        }

        // Too few workers to split: every worker is eligible for both pools
        // (today's shared-pool behavior), not eligible for neither.
        unsafe {
            awkernel_lib::cpu::set_num_cpu(2); // 1 worker only
        }
        assert!(!dag_pool_split_active());
        assert!(is_dag_pool_core(1));
        assert!(is_regular_pool_core(1));
    }

    // Exercises allocate_cluster/release_cluster/admit_dag together in one
    // test: they share the process-global `POOL` static, and `cargo test`
    // runs tests in parallel threads, so splitting this across multiple
    // #[test] fns would risk cross-test interference.
    #[test]
    fn test_cluster_allocation_lifecycle() {
        unsafe {
            // workers 1..10 (9); core 9 is the regular pool, so the DAG pool
            // (1..9) has 8 cores available — matching the "8 available"
            // comments below.
            awkernel_lib::cpu::set_num_cpu(10);
        }

        let heavy_a = allocate_cluster(3).unwrap();
        let heavy_b = allocate_cluster(3).unwrap();
        assert!(!heavy_a.contains(9) && !heavy_b.contains(9)); // never claims the regular-pool core
        assert_eq!(heavy_a.union(heavy_b).iter().count(), 6); // disjoint: 3 + 3 distinct cores
        for cpu in heavy_a.iter() {
            assert!(!heavy_b.contains(cpu));
        }

        // Only 2 workers remain (8 - 3 - 3); a third 3-core cluster must fail.
        match allocate_cluster(3) {
            Err(FederatedError::InsufficientCores {
                required: 3,
                available: 2,
            }) => {}
            other => panic!("expected InsufficientCores{{required: 3, available: 2}}, got {other:?}"),
        }

        release_cluster(heavy_a);
        let heavy_c = allocate_cluster(3).unwrap();
        assert!(heavy_c.iter().all(|cpu| !heavy_b.contains(cpu)));

        // admit_dag end-to-end: Light gets GEDF, Heavy gets a fresh cluster.
        let light = admit_dag(DagAdmissionConfig::from_static(10, 5, 100, 50)).unwrap();
        assert_eq!(light.class, TaskClass::Light);
        assert_eq!(light.source, MetricsSource::Static);
        assert!(matches!(light.scheduler_type, SchedulerType::GEDF(50)));
        release_light_utilization(10, 100); // undo admit_dag's reservation before the next scenario

        release_cluster(heavy_b);
        release_cluster(heavy_c);

        // Light-pool oversubscription: claim 7 of the 8 workers for a heavy
        // cluster, leaving exactly 1 core (100% = 1_000_000 scaled) for the
        // light pool.
        let heavy_big = allocate_cluster(7).unwrap();

        reserve_light_utilization(60, 100).unwrap(); // u = 0.6, committed = 600_000

        match reserve_light_utilization(50, 100) {
            // u = 0.5 => additional 500_000; 600_000 + 500_000 > 1_000_000
            Err(FederatedError::LightPoolOversubscribed {
                additional_utilization_scaled: 500_000,
                available_capacity_scaled: 400_000,
            }) => {}
            other => panic!(
                "expected LightPoolOversubscribed{{additional: 500_000, available: 400_000}}, got {other:?}"
            ),
        }

        release_light_utilization(60, 100); // frees the 600_000 back up

        // Now the same 0.5-utilization DAG fits, this time via a
        // human-supplied estimate rather than a static rd_gen value.
        let heavy_config = DagAdmissionConfig::from_measured(50, 10, 100, 90);
        assert!(matches!(
            classify_dag(&heavy_config).unwrap(),
            TaskClass::Light
        ));
        reserve_light_utilization(50, 100).unwrap();
        release_light_utilization(50, 100);

        release_cluster(heavy_big);
    }
}
