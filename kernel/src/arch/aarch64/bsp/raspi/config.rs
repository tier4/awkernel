/// The number of logical CPUs.
pub const CORE_COUNT: usize = 4;

/// The number of NUMA nodes.
pub const CLUSTER_COUNT: usize = 1;

// Topology information.
pub const MAX_CPUS_PER_CLUSTER: usize = 4;
pub const NUM_PWR_DOMAINS: usize = CLUSTER_COUNT + CORE_COUNT;
