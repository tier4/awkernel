//! Memory barrier implementations for AArch64 architecture
use awkernel_aarch64::{dmb_ld, dmb_st, dmb_sy};

pub const BUS_SPACE_BARRIER_READ: u32 = 0x01;
pub const BUS_SPACE_BARRIER_WRITE: u32 = 0x02;

/// Consumer memory barrier - ensures all loads before the barrier complete
/// before any loads after the barrier.
#[inline(always)]
pub fn membar_consumer() {
    dmb_ld();
}

/// Producer memory barrier - ensures all stores before the barrier complete
/// before any stores after the barrier.
#[inline(always)]
pub fn membar_producer() {
    dmb_st();
}

/// Enter critical section memory barrier
#[inline(always)]
pub fn membar_enter() {
    dmb_sy();
}

/// Exit critical section memory barrier
#[inline(always)]
pub fn membar_exit() {
    dmb_sy();
}

/// Full memory synchronization barrier
#[inline(always)]
pub fn membar_sync() {
    dmb_sy();
}

/// Bus space barrier - ensures ordering of MMIO operations
#[inline(always)]
pub fn bus_space_barrier(_flags: u32) {
    dmb_sy()
}
