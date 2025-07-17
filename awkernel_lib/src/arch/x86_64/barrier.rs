//! Memory barrier implementations for x86_64 architecture
use core::arch::asm;

/// Bus space barrier flags
pub const BUS_SPACE_BARRIER_READ: u32 = 0x01;
pub const BUS_SPACE_BARRIER_WRITE: u32 = 0x02;

impl crate::barrier::Barrier for super::X86 {
    #[inline(always)]
    fn membar_enter() {
        unsafe {
            asm!("mfence");
        }
    }

    #[inline(always)]
    fn membar_exit() {
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }

    #[inline(always)]
    fn membar_producer() {
        // It must be sufficient with Release ordering for producer barriers, but we use SeqCst following the C implementation of OpenBSD.
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }

    #[inline(always)]
    fn membar_consumer() {
        // It must be sufficient with Acquire ordering for consumer barriers, but we use SeqCst following the C implementation of OpenBSD.
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }

    #[inline(always)]
    fn membar_sync() {
        unsafe {
            asm!("mfence");
        }
    }

    #[inline(always)]
    fn bus_space_barrier(flags: u32) {
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
}
