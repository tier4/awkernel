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

    fn cpu_counter() -> u64 {
        cpu::pmccntr_el0::get()
    }
}

pub(super) fn init_primary() {
    init_pmc();

    let count = cpu::cntpct_el0::get();
    unsafe { write_volatile(&mut COUNT_START, count) };
}

/// Initialize performance monitor counter.
fn init_pmc() {
    // Enable user-mode access to cycle counters.
    cpu::pmuserenr_el0::set(0b1101);

    // Disable the cycle counter overflow interrupt.
    cpu::pmintenset_el1::set(0);

    // Enable the cycle counter.
    cpu::pmcntenset_el0::set(1 << 31);

    // Clear the cycle counter and start.
    let pmcr_el0 = cpu::pmcr_el0::get();
    let pmcr_el0 = pmcr_el0 | 0b111;
    cpu::isb();
    cpu::pmcr_el0::set(pmcr_el0);

    cpu::pmccfiltr_el0::set(1 << 27);
}

pub(super) fn init_non_primary() {
    init_pmc();
}
