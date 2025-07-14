//! Memory barrier implementations for RISC-V 32-bit architecture
use core::arch::asm;

pub const BUS_SPACE_BARRIER_READ: u32 = 0x01;
pub const BUS_SPACE_BARRIER_WRITE: u32 = 0x02;

/// Consumer memory barrier - ensures all loads before the barrier complete
/// before any loads after the barrier.
#[inline(always)]
pub fn membar_consumer() {
    unsafe {
        asm!("fence r,r");
    }
}

/// Producer memory barrier - ensures all stores before the barrier complete
/// before any stores after the barrier.
#[inline(always)]
pub fn membar_producer() {
    unsafe {
        asm!("fence w,w");
    }
}

/// Enter critical section memory barrier
#[inline(always)]
pub fn membar_enter() {
    unsafe {
        asm!("fence w,rw");
    }
}

/// Exit critical section memory barrier
#[inline(always)]
pub fn membar_exit() {
    unsafe {
        asm!("fence rw,w");
    }
}

/// Full memory synchronization barrier
#[inline(always)]
pub fn membar_sync() {
    unsafe {
        asm!("fence rw,rw");
    }
}

/// Bus space barrier - ensures ordering of MMIO operations
#[inline(always)]
pub fn bus_space_barrier(_flags: u32) {
    unsafe {
        asm!("fence iorw,iorw");
    }
}
