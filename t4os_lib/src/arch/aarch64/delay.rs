use crate::delay::Delay;
use core::ptr::{read_volatile, write_volatile};
use t4os_aarch64;

pub(crate) struct ArchDelay;

static mut COUNT_START: u64 = 0;

impl Delay for ArchDelay {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("wfi") };
    }

    fn wait_microsec(usec: u64) {
        let frq = t4os_aarch64::cntfrq_el0::get();
        let t = t4os_aarch64::cntpct_el0::get();

        let end = t + ((frq / 1000) * usec) / 1000;

        while t4os_aarch64::cntpct_el0::get() < end {
            t4os_aarch64::isb();
        }
    }

    fn uptime() -> u64 {
        let start = unsafe { read_volatile(&COUNT_START) };

        let frq = t4os_aarch64::cntfrq_el0::get();
        let now = t4os_aarch64::cntpct_el0::get();

        let diff = now - start;

        diff * 1_000_000 / frq
    }

    fn cpu_counter() -> u64 {
        t4os_aarch64::pmccntr_el0::get()
    }
}

pub(super) fn init_primary() {
    init_pmc();

    let count = t4os_aarch64::cntpct_el0::get();
    unsafe { write_volatile(&mut COUNT_START, count) };
}

/// Initialize performance monitor counter.
fn init_pmc() {
    // Enable user-mode access to cycle counters.
    t4os_aarch64::pmuserenr_el0::set(0b1101);

    // Disable the cycle counter overflow interrupt.
    t4os_aarch64::pmintenset_el1::set(0);

    // Enable the cycle counter.
    t4os_aarch64::pmcntenset_el0::set(1 << 31);

    // Clear the cycle counter and start.
    let pmcr_el0 = t4os_aarch64::pmcr_el0::get();
    let pmcr_el0 = pmcr_el0 | 0b111;
    t4os_aarch64::isb();
    t4os_aarch64::pmcr_el0::set(pmcr_el0);

    t4os_aarch64::pmccfiltr_el0::set(1 << 27);
}

pub(super) fn init_non_primary() {
    init_pmc();
}
