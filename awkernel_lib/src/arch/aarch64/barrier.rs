//! Memory barrier implementations for AArch64 architecture
use awkernel_aarch64::{dmb_ld, dmb_st, dmb_sy};

pub const BUS_SPACE_BARRIER_READ: u32 = 0x01;
pub const BUS_SPACE_BARRIER_WRITE: u32 = 0x02;

impl crate::barrier::Barrier for super::AArch64 {
    #[inline(always)]
    fn membar_enter() {
        dmb_sy();
    }

    #[inline(always)]
    fn membar_exit() {
        dmb_sy();
    }

    #[inline(always)]
    fn membar_producer() {
        dmb_st();
    }

    #[inline(always)]
    fn membar_consumer() {
        dmb_ld();
    }

    #[inline(always)]
    fn membar_sync() {
        dmb_sy();
    }

    #[inline(always)]
    fn bus_space_barrier(_flags: u32) {
        dmb_sy();
    }
}
