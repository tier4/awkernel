use crate::delay::Delay;

use super::cpu;

pub struct ArchDelay;

impl Delay for ArchDelay {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("wfi") };
    }

    fn wait_microsec(usec: u32) {
        let frq = cpu::cntfrq_el0::get();
        let t = cpu::cntpct_el0::get();

        let end = t + ((frq / 1000) * usec as u64) / 1000;

        while cpu::cntpct_el0::get() < end {
            cpu::isb();
        }
    }
}
