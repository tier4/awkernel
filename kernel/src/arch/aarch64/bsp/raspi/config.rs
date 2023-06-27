/// The number of logical CPUs.
pub const CORE_COUNT: usize = 4;

/// The number of NUMA nodes.
pub const CLUSTER_COUNT: usize = 1;

// Topology information.
pub const MAX_CPUS_PER_CLUSTER: usize = 4;
pub const _NUM_PWR_DOMAINS: usize = CLUSTER_COUNT + CORE_COUNT;

#[cfg(feature = "raspi3")]
pub const UART_IRQ: u16 = 57;

#[cfg(feature = "raspi4")]
pub const UART_IRQ: u16 = 121 + 32;

pub const UART_CLOCK: usize = 48000000;

#[cfg(feature = "raspi3")]
pub const PREEMPT_IRQ: u16 = !0; // TODO

#[cfg(feature = "raspi4")]
pub const PREEMPT_IRQ: u16 = 0;
