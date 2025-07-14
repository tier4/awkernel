//! Memory barrier implementations for x86_64 architecture

use core::arch::x86_64::{_mm_lfence, _mm_mfence, _mm_sfence};

/// Bus space barrier flags
pub const BUS_SPACE_BARRIER_READ: u32 = 0x01;
pub const BUS_SPACE_BARRIER_WRITE: u32 = 0x02;

/// Consumer memory barrier - ensures all loads before the barrier complete
/// before any loads after the barrier.
#[inline(always)]
pub fn membar_consumer() {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Producer memory barrier - ensures all stores before the barrier complete
/// before any stores after the barrier.
#[inline(always)]
pub fn membar_producer() {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::Release);
}

/// Enter critical section memory barrier
#[inline(always)]
pub fn membar_enter() {
    unsafe { _mm_mfence() }
}

/// Exit critical section memory barrier
#[inline(always)]
pub fn membar_exit() {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Full memory synchronization barrier
#[inline(always)]
pub fn membar_sync() {
    unsafe { _mm_mfence() }
}

/// Bus space barrier - ensures ordering of MMIO operations
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
