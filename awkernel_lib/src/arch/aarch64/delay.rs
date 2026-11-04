use crate::delay::Delay;
use core::ptr::{addr_of, addr_of_mut, read_volatile, write_volatile};

static mut COUNT_START: u64 = 0;

impl Delay for super::AArch64 {
    #[inline(always)]
    fn wait_interrupt() {
        unsafe { core::arch::asm!("wfi") };
    }

    fn wait_microsec(usec: u64) {
        let frq = super::utils::cntfrq_el0::get();
        let t = super::utils::cntvct_el0::get();

        let end = t + ((frq / 1000) * usec) / 1000;

        while super::utils::cntvct_el0::get() < end {
            super::utils::isb();
        }
    }

    fn uptime() -> u64 {
        let start = unsafe { read_volatile(addr_of!(COUNT_START)) };

        let frq = super::utils::cntfrq_el0::get();
        let now = super::utils::cntvct_el0::get();

        let diff = now - start;

        diff * 1_000_000 / frq
    }

    fn uptime_nano() -> u128 {
        let start = unsafe { read_volatile(addr_of!(COUNT_START)) };

        let frq = super::utils::cntfrq_el0::get();
        let now = super::utils::cntvct_el0::get();

        let diff = now - start;

        diff as u128 * 1_000_000_000 / frq as u128
    }

    fn cpu_counter() -> u64 {
        super::utils::pmccntr_el0::get()
    }
}

pub(super) unsafe fn init_primary() {
    init_pmc();

    let count = super::utils::cntvct_el0::get();
    write_volatile(addr_of_mut!(COUNT_START), count);
}

/// Initialize performance monitor counter.
unsafe fn init_pmc() {
    // Enable user-mode access to cycle counters.
    super::utils::pmuserenr_el0::set(0b1101);

    // Disable the cycle counter overflow interrupt.
    super::utils::pmintenset_el1::set(0);

    // Enable the cycle counter.
    super::utils::pmcntenset_el0::set(1 << 31);

    // Clear the cycle counter and start.
    let pmcr_el0 = super::utils::pmcr_el0::get();
    let pmcr_el0 = pmcr_el0 | 0b111;
    super::utils::isb();
    super::utils::pmcr_el0::set(pmcr_el0);

    super::utils::pmccfiltr_el0::set(1 << 27);
}

pub(super) unsafe fn init_non_primary() {
    init_pmc();
}
