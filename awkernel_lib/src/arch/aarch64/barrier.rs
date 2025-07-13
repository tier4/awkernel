//! Memory barrier implementations for AArch64 architecture
//! 
//! This module provides memory barrier functions compatible with OpenBSD's
//! membar_* and bus_space_barrier functions.

use awkernel_aarch64::{dmb_ld, dmb_st, dmb_sy, dsb_ld, dsb_st, dsb_sy};

/// Bus space barrier flags (from OpenBSD)
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/arm64/include/bus.h
pub const BUS_SPACE_BARRIER_READ: u32 = 0x01;
pub const BUS_SPACE_BARRIER_WRITE: u32 = 0x02;

/// Consumer memory barrier - ensures all loads before the barrier complete
/// before any loads after the barrier.
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/arm64/include/atomic.h
/// On ARM64, membar_consumer() uses "dmb ld" (Data Memory Barrier Load)
#[inline(always)]
pub fn membar_consumer() {
    dmb_ld();
}

/// Producer memory barrier - ensures all stores before the barrier complete
/// before any stores after the barrier.
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/arm64/include/atomic.h
/// On ARM64, membar_producer() uses "dmb st" (Data Memory Barrier Store)
#[inline(always)]
pub fn membar_producer() {
    dmb_st();
}

/// Enter critical section memory barrier
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/arm64/include/atomic.h
/// On ARM64, membar_enter() uses "dmb sy" (full barrier)
#[inline(always)]
pub fn membar_enter() {
    dmb_sy();
}

/// Exit critical section memory barrier
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/arm64/include/atomic.h
/// On ARM64, membar_exit() uses "dmb sy" (full barrier)
#[inline(always)]
pub fn membar_exit() {
    dmb_sy();
}

/// Full memory synchronization barrier
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/arm64/include/atomic.h
/// On ARM64, membar_sync() uses "dmb sy" (full barrier)
#[inline(always)]
pub fn membar_sync() {
    dmb_sy();
}

/// Bus space barrier - ensures ordering of MMIO operations
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/arm64/include/bus.h
/// ARM64 uses different DMB (Data Memory Barrier) instructions based on flags
/// 
/// # Arguments
/// * `flags` - Combination of BUS_SPACE_BARRIER_READ and/or BUS_SPACE_BARRIER_WRITE
#[inline(always)]
pub fn bus_space_barrier(flags: u32) {
    match flags {
        f if f == (BUS_SPACE_BARRIER_READ | BUS_SPACE_BARRIER_WRITE) => {
            // Both read and write barrier - use dmb sy (system)
            dmb_sy();
        }
        BUS_SPACE_BARRIER_WRITE => {
            // Write barrier only - use dmb st (store)
            dmb_st();
        }
        BUS_SPACE_BARRIER_READ => {
            // Read barrier only - use dmb ld (load)
            dmb_ld();
        }
        _ => {
            // Default case - use full barrier
            dmb_sy();
        }
    }
}

/// Device memory barrier for stronger ordering guarantees
/// 
/// Uses DSB (Data Synchronization Barrier) which is stronger than DMB
/// This ensures completion of memory accesses before proceeding
#[inline(always)]
pub fn device_barrier(flags: u32) {
    match flags {
        f if f == (BUS_SPACE_BARRIER_READ | BUS_SPACE_BARRIER_WRITE) => {
            // Both read and write barrier - use dsb sy
            dsb_sy();
        }
        BUS_SPACE_BARRIER_WRITE => {
            // Write barrier only - use dsb st
            dsb_st();
        }
        BUS_SPACE_BARRIER_READ => {
            // Read barrier only - use dsb ld
            dsb_ld();
        }
        _ => {
            // Default case - use full barrier
            dsb_sy();
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

    #[test]
    fn test_device_barrier() {
        device_barrier(BUS_SPACE_BARRIER_READ);
        device_barrier(BUS_SPACE_BARRIER_WRITE);
        device_barrier(BUS_SPACE_BARRIER_READ | BUS_SPACE_BARRIER_WRITE);
    }
}