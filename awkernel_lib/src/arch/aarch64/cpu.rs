use crate::cpu::CPU;
use awkernel_aarch64::mpidr_el1;
use core::sync::atomic::{AtomicUsize, Ordering};

static MAX_CPUS_PER_CLUSTER: AtomicUsize = AtomicUsize::new(0);
static CLUSTER_COUNT: AtomicUsize = AtomicUsize::new(0);

pub fn set_cluster_info(max_cpus_per_cluster: usize, cluster_count: usize) {
    MAX_CPUS_PER_CLUSTER.store(max_cpus_per_cluster, Ordering::Relaxed);
    CLUSTER_COUNT.store(cluster_count, Ordering::Relaxed);
}

/// get core index from MPIDR
fn core_pos_by_mpidr(mpidr: usize) -> Option<usize> {
    let core = mpidr & 0xFF;
    let cluster = (mpidr >> 8) & 0xFF;
    let lvl2 = (mpidr >> 16) & 0xFF;
    let lvl3 = (mpidr >> 32) & 0xFF;

    if lvl2 > 0
        || lvl3 > 0
        || cluster >= CLUSTER_COUNT.load(Ordering::Relaxed)
        || core >= MAX_CPUS_PER_CLUSTER.load(Ordering::Relaxed)
    {
        None
    } else {
        Some(core)
    }
}

pub(crate) struct ArchCPU;

impl CPU for ArchCPU {
    fn cpu_id() -> usize {
        let mpidr = mpidr_el1::get();
        core_pos_by_mpidr(mpidr as usize).unwrap()
    }
}
