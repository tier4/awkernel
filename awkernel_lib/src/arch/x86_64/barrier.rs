//! Memory barrier implementations for x86_64 architecture
//! 
//! This module provides memory barrier functions compatible with OpenBSD's
//! membar_* and bus_space_barrier functions.

use core::arch::x86_64::{_mm_lfence, _mm_mfence, _mm_sfence};

/// Bus space barrier flags (from OpenBSD)
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/amd64/include/bus.h
pub const BUS_SPACE_BARRIER_READ: u32 = 0x01;
pub const BUS_SPACE_BARRIER_WRITE: u32 = 0x02;

/// Consumer memory barrier - ensures all loads before the barrier complete
/// before any loads after the barrier.
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/amd64/include/atomic.h
/// On x86_64, membar_consumer() is defined as __membar("") which expands to:
/// __asm volatile("" ::: "memory")
/// This is sufficient because x86 has Total Store Order (TSO) - loads are never reordered
#[inline(always)]
pub fn membar_consumer() {
    // Direct translation of OpenBSD's __membar("")
    // In Rust, we need to use compiler_fence to get the same "memory" clobber effect
    // as __asm volatile("" ::: "memory") in C
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Producer memory barrier - ensures all stores before the barrier complete
/// before any stores after the barrier.
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/amd64/include/atomic.h
/// On x86_64, membar_producer() is also just a compiler barrier due to TSO
#[inline(always)]
pub fn membar_producer() {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::Release);
}

/// Enter critical section memory barrier
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/amd64/include/atomic.h
/// On x86_64, membar_enter() is just a compiler barrier
#[inline(always)]
pub fn membar_enter() {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Exit critical section memory barrier
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/amd64/include/atomic.h
/// On x86_64, membar_exit() is just a compiler barrier
#[inline(always)]
pub fn membar_exit() {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Full memory synchronization barrier
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/amd64/include/atomic.h
/// On x86_64, membar_sync() uses mfence for full synchronization
#[inline(always)]
pub fn membar_sync() {
    unsafe { _mm_mfence() }
}

/// Bus space barrier - ensures ordering of MMIO operations
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/amd64/include/bus.h
/// The x86_64 implementation uses different fence instructions based on flags:
/// - READ|WRITE: mfence
/// - WRITE only: sfence
/// - READ only (or default): lfence
/// 
/// # Arguments
/// * `flags` - Combination of BUS_SPACE_BARRIER_READ and/or BUS_SPACE_BARRIER_WRITE
#[inline(always)]
pub fn bus_space_barrier(flags: u32) {
    match flags {
        f if f == (BUS_SPACE_BARRIER_READ | BUS_SPACE_BARRIER_WRITE) => {
            // Both read and write barrier - use mfence
            unsafe { _mm_mfence() }
        }
        BUS_SPACE_BARRIER_WRITE => {
            // Write barrier only - use sfence
            unsafe { _mm_sfence() }
        }
        _ => {
            // Default case (includes READ) - use lfence
            unsafe { _mm_lfence() }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_membar_functions() {
        // Just ensure they compile and run without panicking
        membar_consumer();
        membar_producer();
        membar_enter();
        membar_exit();
        membar_sync();
    }

    #[test]
    fn test_bus_space_barrier() {
        bus_space_barrier(BUS_SPACE_BARRIER_READ);
        bus_space_barrier(BUS_SPACE_BARRIER_WRITE);
        bus_space_barrier(BUS_SPACE_BARRIER_READ | BUS_SPACE_BARRIER_WRITE);
        bus_space_barrier(0); // Default case
    }
}