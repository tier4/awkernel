//! Memory barrier implementations for x86_64 architecture
use core::arch::asm;

/// Bus space barrier flags
pub const BUS_SPACE_BARRIER_READ: u32 = 0x01;
pub const BUS_SPACE_BARRIER_WRITE: u32 = 0x02;

/// Enter critical section memory barrier
#[inline(always)]
pub fn membar_enter() {
    unsafe {
        asm!("mfence");
    }
}

/// Exit critical section memory barrier
#[inline(always)]
pub fn membar_exit() {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Producer memory barrier - ensures all stores before the barrier complete
/// before any stores after the barrier.
#[inline(always)]
pub fn membar_producer() {
    // It must be suffecient with Release ordering for producer barriers, but we use SeqCst following the C implementation of OpenBSD.
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Consumer memory barrier - ensures all loads before the barrier complete
/// before any loads after the barrier.
#[inline(always)]
pub fn membar_consumer() {
    // It must be suffecient with Acquire ordering for producer barriers, but we use SeqCst following the C implementation of OpenBSD.
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Full memory synchronization barrier
#[inline(always)]
pub fn membar_sync() {
    unsafe {
        asm!("mfence");
    }
}

/// Bus space barrier - ensures ordering of MMIO operations
#[inline(always)]
pub fn bus_space_barrier(flags: u32) {
    match flags {
        f if f == (BUS_SPACE_BARRIER_READ | BUS_SPACE_BARRIER_WRITE) => unsafe {
            asm!("mfence");
        },
        BUS_SPACE_BARRIER_WRITE => unsafe {
            asm!("sfence");
        },
        _ => unsafe {
            asm!("lfence");
        },
    }
}
