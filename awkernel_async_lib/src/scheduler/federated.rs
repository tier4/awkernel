//! Federated Scheduling admission layer (Li et al., RTSS 2014) for DAG tasks.
//!
//! Federated Scheduling classifies a DAG by utilization `u = C/T`:
//! - **Heavy** (`u > 1`): given an exclusive cluster of `m` cores.
//! - **Light** (`u <= 1`): shares the remaining cores with other light DAGs.
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
//! [`admit_dag`] is the single entry point: given a DAG's WCET volume/
//! critical-path ([`DagMetrics`]) and its period/deadline ([`FederatedTiming`]),
//! it returns the [`SchedulerType`] every node of that DAG should be
//! registered with.

use awkernel_lib::{
    cpu::{num_cpu, CpuSet},
    sync::mutex::{MCSNode, Mutex},
};

use alloc::vec::Vec;

use super::SchedulerType;

/// Source of a DAG's WCET volume (`C`) and critical-path length (`L`).
///
/// The classification and core-count math (see [`classify_dag`]) is
/// identical regardless of variant; this only records provenance, e.g. for
/// logging which DAGs are scheduled from a priori knowledge versus
/// observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DagMetrics {
    /// Computed ahead of time from a fully-known static DAG structure, e.g.
    /// a topological-sort DP over per-node WCET declared in an `rd_gen`
    /// YAML file (see `rd_gen_to_dags::dag_stats::compute_dag_stats`).
    Static { volume: u64, critical_path: u64 },
    /// Derived from runtime measurement of a DAG whose structure/WCET is not
    /// fully known ahead of admission.
    Measured { volume: u64, critical_path: u64 },
}

impl DagMetrics {
    pub const fn volume(&self) -> u64 {
        match self {
            DagMetrics::Static { volume, .. } | DagMetrics::Measured { volume, .. } => *volume,
        }
    }

    pub const fn critical_path(&self) -> u64 {
        match self {
            DagMetrics::Static { critical_path, .. }
            | DagMetrics::Measured { critical_path, .. } => *critical_path,
        }
    }
}

/// `period` (`T`) and `relative_deadline` (`D`) of a DAG, in the same time
/// unit as [`SchedulerType::GEDF`]/[`SchedulerType::ClusteredEDF`]'s
/// `relative_deadline` parameter (this crate's scheduler layer treats it as
/// an opaque `u64`; callers must stay consistent, exactly as those two
/// variants already require).
///
/// `T` drives heavy/light classification (`u = C/T`); `D` drives the
/// heavy-cluster core count and is handed to the resulting `SchedulerType`,
/// which computes the actual per-instance *absolute* deadline itself
/// (`wake_time + D`, shared across every node of one DAG instance) the first
/// time it is needed — this struct only carries the two relative quantities.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FederatedTiming {
    pub period: u64,
    pub relative_deadline: u64,
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
pub fn classify_dag(
    metrics: &DagMetrics,
    timing: &FederatedTiming,
) -> Result<TaskClass, FederatedError> {
    let critical_path = metrics.critical_path();

    if timing.relative_deadline <= critical_path {
        return Err(FederatedError::Infeasible {
            critical_path,
            relative_deadline: timing.relative_deadline,
        });
    }

    let volume = metrics.volume();
    if !is_heavy(volume, timing.period) {
        return Ok(TaskClass::Light);
    }

    let Some(required_cores) = required_cores(volume, critical_path, timing.relative_deadline)
    else {
        return Err(FederatedError::Infeasible {
            critical_path,
            relative_deadline: timing.relative_deadline,
        });
    };

    Ok(TaskClass::Heavy { required_cores })
}

/// Cores currently claimed by some heavy DAG's exclusive cluster. Disjoint
/// from (and unrelated to) `NUM_CLUSTERED_TASKS_ALIVE`: that counter tracks
/// live *tasks* per CPU once spawned, while this tracks which worker CPUs
/// this module has already promised to a cluster, so two heavy DAGs never
/// get the same core.
static CLAIMED_CORES: Mutex<CpuSet> = Mutex::new(CpuSet::empty());

/// Claim `required_cores` worker CPUs (`1..num_cpu()`, CPU 0 is the primary
/// core and never eligible) not already claimed by another heavy cluster.
pub fn allocate_cluster(required_cores: u16) -> Result<CpuSet, FederatedError> {
    let required = required_cores as usize;

    let mut node = MCSNode::new();
    let mut claimed = CLAIMED_CORES.lock(&mut node);

    let free_workers: Vec<usize> = (1..num_cpu())
        .filter(|cpu| !claimed.contains(*cpu))
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

    *claimed = claimed.union(cluster);
    Ok(cluster)
}

/// Release a cluster previously returned by [`allocate_cluster`], making its
/// cores available to the next heavy DAG admitted.
pub fn release_cluster(cluster: CpuSet) {
    let mut node = MCSNode::new();
    let mut claimed = CLAIMED_CORES.lock(&mut node);
    for cpu in cluster.iter() {
        claimed.remove(cpu);
    }
}

/// Admit a DAG: classify it and decide the `SchedulerType` every one of its
/// nodes should be registered with. For a heavy DAG this also allocates its
/// exclusive cluster (release it with [`release_cluster`] once the DAG is
/// torn down, if ever — none of this test bed's DAGs currently are).
pub fn admit_dag(
    metrics: DagMetrics,
    timing: FederatedTiming,
) -> Result<FederatedAssignment, FederatedError> {
    match classify_dag(&metrics, &timing)? {
        TaskClass::Light => Ok(FederatedAssignment {
            class: TaskClass::Light,
            scheduler_type: SchedulerType::GEDF(timing.relative_deadline),
        }),
        TaskClass::Heavy { required_cores } => {
            let cluster = allocate_cluster(required_cores)?;
            Ok(FederatedAssignment {
                class: TaskClass::Heavy { required_cores },
                scheduler_type: SchedulerType::ClusteredEDF(timing.relative_deadline, cluster),
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
        let metrics = DagMetrics::Static {
            volume: 10,
            critical_path: 50,
        };
        let timing = FederatedTiming {
            period: 1000,
            relative_deadline: 50, // == critical_path
        };
        assert_eq!(
            classify_dag(&metrics, &timing),
            Err(FederatedError::Infeasible {
                critical_path: 50,
                relative_deadline: 50,
            })
        );
    }

    #[test]
    fn test_classify_dag_light() {
        let metrics = DagMetrics::Static {
            volume: 80,
            critical_path: 20,
        };
        let timing = FederatedTiming {
            period: 100, // volume(80) <= period(100) => Light
            relative_deadline: 90,
        };
        assert_eq!(classify_dag(&metrics, &timing), Ok(TaskClass::Light));
    }

    #[test]
    fn test_classify_dag_heavy() {
        let metrics = DagMetrics::Static {
            volume: 100,
            critical_path: 20,
        };
        let timing = FederatedTiming {
            period: 50, // volume(100) > period(50) => Heavy
            relative_deadline: 50,
        };
        assert_eq!(
            classify_dag(&metrics, &timing),
            Ok(TaskClass::Heavy { required_cores: 3 }) // ceil((100-20)/(50-20)) = 3
        );
    }

    // Exercises allocate_cluster/release_cluster/admit_dag together in one
    // test: they share the process-global `CLAIMED_CORES` static, and
    // `cargo test` runs tests in parallel threads, so splitting this across
    // multiple #[test] fns would risk cross-test interference.
    #[test]
    fn test_cluster_allocation_lifecycle() {
        unsafe {
            awkernel_lib::cpu::set_num_cpu(9); // cores 0..9, workers 1..9 (8 available)
        }

        let heavy_a = allocate_cluster(3).unwrap();
        let heavy_b = allocate_cluster(3).unwrap();
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
        let light = admit_dag(
            DagMetrics::Static {
                volume: 10,
                critical_path: 5,
            },
            FederatedTiming {
                period: 100,
                relative_deadline: 50,
            },
        )
        .unwrap();
        assert_eq!(light.class, TaskClass::Light);
        assert!(matches!(light.scheduler_type, SchedulerType::GEDF(50)));

        release_cluster(heavy_b);
        release_cluster(heavy_c);
    }
}
