//! Memory barrier implementations for RISC-V 64-bit architecture
//! 
//! This module provides memory barrier functions compatible with OpenBSD's
//! membar_* and bus_space_barrier functions.

use core::arch::asm;

/// Bus space barrier flags (from OpenBSD)
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/riscv64/include/bus.h
pub const BUS_SPACE_BARRIER_READ: u32 = 0x01;
pub const BUS_SPACE_BARRIER_WRITE: u32 = 0x02;

/// Consumer memory barrier - ensures all loads before the barrier complete
/// before any loads after the barrier.
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/riscv64/include/atomic.h
/// On RISC-V, membar_consumer() uses "fence r,rw" (read fence)
#[inline(always)]
pub fn membar_consumer() {
    unsafe {
        asm!("fence r,rw", options(nostack));
    }
}

/// Producer memory barrier - ensures all stores before the barrier complete
/// before any stores after the barrier.
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/riscv64/include/atomic.h
/// On RISC-V, membar_producer() uses "fence rw,w" (write fence)
#[inline(always)]
pub fn membar_producer() {
    unsafe {
        asm!("fence rw,w", options(nostack));
    }
}

/// Enter critical section memory barrier
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/riscv64/include/atomic.h
/// On RISC-V, membar_enter() uses "fence rw,rw" (full fence)
#[inline(always)]
pub fn membar_enter() {
    unsafe {
        asm!("fence rw,rw", options(nostack));
    }
}

/// Exit critical section memory barrier
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/riscv64/include/atomic.h
/// On RISC-V, membar_exit() uses "fence rw,rw" (full fence)
#[inline(always)]
pub fn membar_exit() {
    unsafe {
        asm!("fence rw,rw", options(nostack));
    }
}

/// Full memory synchronization barrier
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/riscv64/include/atomic.h
/// On RISC-V, membar_sync() uses "fence iorw,iorw" (full I/O and memory fence)
#[inline(always)]
pub fn membar_sync() {
    unsafe {
        asm!("fence iorw,iorw", options(nostack));
    }
}

/// Bus space barrier - ensures ordering of MMIO operations
/// 
/// Reference: https://github.com/openbsd/src/blob/master/sys/arch/riscv64/include/bus.h
/// RISC-V uses fence instructions with different ordering constraints
/// 
/// # Arguments
/// * `flags` - Combination of BUS_SPACE_BARRIER_READ and/or BUS_SPACE_BARRIER_WRITE
#[inline(always)]
pub fn bus_space_barrier(flags: u32) {
    match flags {
        f if f == (BUS_SPACE_BARRIER_READ | BUS_SPACE_BARRIER_WRITE) => {
            // Both read and write barrier - full fence
            unsafe {
                asm!("fence iorw,iorw", options(nostack));
            }
        }
        BUS_SPACE_BARRIER_WRITE => {
            // Write barrier only - fence for writes
            unsafe {
                asm!("fence w,w", options(nostack));
            }
        }
        BUS_SPACE_BARRIER_READ => {
            // Read barrier only - fence for reads
            unsafe {
                asm!("fence r,r", options(nostack));
            }
        }
        _ => {
            // Default case - use full fence
            unsafe {
                asm!("fence iorw,iorw", options(nostack));
            }
        }
    }
}

/// Device memory barrier - ensures ordering of device I/O operations
/// 
/// On RISC-V, this uses fence.i for instruction synchronization when needed
#[inline(always)]
pub fn device_barrier() {
    unsafe {
        asm!("fence iorw,iorw", options(nostack));
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
        device_barrier();
    }
}