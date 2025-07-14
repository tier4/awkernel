//! Memory barrier abstractions for device drivers
//!
//! This module provides architecture-independent memory barrier functions
//! that are essential for device driver development, particularly for MMIO operations.

#[cfg(not(feature = "std"))]
use crate::arch::ArchImpl;

/// Bus space barrier flags
pub const BUS_SPACE_BARRIER_READ: u32 = 0x01;
pub const BUS_SPACE_BARRIER_WRITE: u32 = 0x02;

pub trait Barrier {
    /// Enter critical section memory barrier
    fn membar_enter();

    /// Exit critical section memory barrier
    fn membar_exit();

    /// Producer memory barrier - ensures all stores before the barrier complete
    /// before any stores after the barrier.
    fn membar_producer();

    /// Consumer memory barrier - ensures all loads before the barrier complete
    /// before any loads after the barrier.
    fn membar_consumer();

    /// Full memory synchronization barrier
    fn membar_sync();

    /// Bus space barrier - ensures ordering of MMIO operations
    fn bus_space_barrier(flags: u32);
}

/// Enter critical section memory barrier
#[cfg(not(feature = "std"))]
#[inline(always)]
pub fn membar_enter() {
    ArchImpl::membar_enter();
}

/// Exit critical section memory barrier
#[cfg(not(feature = "std"))]
#[inline(always)]
pub fn membar_exit() {
    ArchImpl::membar_exit();
}

/// Producer memory barrier - ensures all stores before the barrier complete
/// before any stores after the barrier.
#[cfg(not(feature = "std"))]
#[inline(always)]
pub fn membar_producer() {
    ArchImpl::membar_producer();
}

/// Consumer memory barrier - ensures all loads before the barrier complete
/// before any loads after the barrier.
#[cfg(not(feature = "std"))]
#[inline(always)]
pub fn membar_consumer() {
    ArchImpl::membar_consumer();
}

/// Full memory synchronization barrier
#[cfg(not(feature = "std"))]
#[inline(always)]
pub fn membar_sync() {
    ArchImpl::membar_sync();
}

/// Bus space barrier - ensures ordering of MMIO operations
#[cfg(not(feature = "std"))]
#[inline(always)]
pub fn bus_space_barrier(flags: u32) {
    ArchImpl::bus_space_barrier(flags);
}
