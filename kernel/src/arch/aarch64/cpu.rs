use t4os_aarch64::mpidr_el1;

use super::config;

pub const MAX_CPUS_PER_CLUSTER: usize = config::MAX_CPUS_PER_CLUSTER;
pub const CLUSTER_COUNT: usize = config::CLUSTER_COUNT;

/// get core index from MPIDR
fn core_pos_by_mpidr(mpidr: usize) -> Option<usize> {
    let core = mpidr & 0xFF;
    let cluster = (mpidr >> 8) & 0xFF;
    let lvl2 = (mpidr >> 16) & 0xFF;
    let lvl3 = (mpidr >> 32) & 0xFF;

    if lvl2 > 0 || lvl3 > 0 || cluster >= CLUSTER_COUNT || core >= MAX_CPUS_PER_CLUSTER {
        None
    } else {
        Some(core)
    }
}

/// get my core index
pub fn core_pos() -> usize {
    let mpidr = mpidr_el1::get();
    core_pos_by_mpidr(mpidr as usize).unwrap()
}
