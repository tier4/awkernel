use core::ptr::{read_volatile, write_volatile};

use crate::delay::Delay;

use super::cpu;

pub struct ArchDelay;

static mut COUNT_START: u64 = 0;

impl Delay for ArchDelay {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("wfi") };
    }

    fn wait_microsec(usec: u64) {
        let frq = cpu::cntfrq_el0::get();
        let t = cpu::cntpct_el0::get();

        let end = t + ((frq / 1000) * usec) / 1000;

        while cpu::cntpct_el0::get() < end {
            cpu::isb();
        }
    }

    fn uptime() -> u64 {
        let start = unsafe { read_volatile(&COUNT_START) };

        let frq = cpu::cntfrq_el0::get();
        let now = cpu::cntpct_el0::get();

        let diff = now - start;

        diff * 1000_000 / frq
    }
}

pub(super) fn init() {
    let count = cpu::cntpct_el0::get();
    unsafe { write_volatile(&mut COUNT_START, count) };
}
