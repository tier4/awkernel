//! Memory barrier implementations for RISC-V 32-bit architecture
use core::arch::asm;

pub const BUS_SPACE_BARRIER_READ: u32 = 0x01;
pub const BUS_SPACE_BARRIER_WRITE: u32 = 0x02;

impl crate::barrier::Barrier for super::RV32 {
    #[inline(always)]
    fn membar_enter() {
        unsafe {
            asm!("fence w,rw");
        }
    }

    #[inline(always)]
    fn membar_exit() {
        unsafe {
            asm!("fence rw,w");
        }
    }

    #[inline(always)]
    fn membar_producer() {
        unsafe {
            asm!("fence w,w");
        }
    }

    #[inline(always)]
    fn membar_consumer() {
        unsafe {
            asm!("fence r,r");
        }
    }

    #[inline(always)]
    fn membar_sync() {
        unsafe {
            asm!("fence rw,rw");
        }
    }

    #[inline(always)]
    fn bus_space_barrier(_flags: u32) {
        unsafe {
            asm!("fence iorw,iorw");
        }
    }
}
