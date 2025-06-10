use crate::delay::Delay;
use core::ptr::{addr_of, addr_of_mut, read_volatile, write_volatile};

// we should get this info from device tree
const ACLINT_MTIME_BASE: u32 = 0x0200_0000 + 0x0000bff8;
const RISCV_TIMEBASE_FREQ: u64 = 10_000_000;

static mut COUNT_START: u64 = 0;

impl Delay for super::RV64 {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("wfi") };
    }

    fn wait_microsec(usec: u64) {
        let mtime = ACLINT_MTIME_BASE as *const u64;
        let end = unsafe { *mtime + ((RISCV_TIMEBASE_FREQ / 1000) * usec) / 1000 };
        while unsafe { core::ptr::read_volatile(mtime) < end } {}
    }

    fn uptime() -> u64 {
        let start = unsafe { read_volatile(addr_of!(COUNT_START)) };
        let mtime = ACLINT_MTIME_BASE as *const u64;
        let now = unsafe { core::ptr::read_volatile(mtime) };
        let diff = now - start;
        diff * 1_000_000 / RISCV_TIMEBASE_FREQ
    }

    fn uptime_nano() -> u128 {
        let start = unsafe { read_volatile(addr_of!(COUNT_START)) };
        let mtime = ACLINT_MTIME_BASE as *const u64;
        let now = unsafe { core::ptr::read_volatile(mtime) };
        let diff = now - start;
        diff as u128 * 1_000_000_000 / RISCV_TIMEBASE_FREQ as u128
    }

    fn cpu_counter() -> u64 {
        let cycle: u64;
        unsafe {
            core::arch::asm!("rdcycle {}", out(reg) cycle);
        }
        cycle
    }
}

pub(super) unsafe fn init_primary() {
    let mtime = ACLINT_MTIME_BASE as *const u64;
    let count = core::ptr::read_volatile(mtime);
    write_volatile(addr_of_mut!(COUNT_START), count);
}

pub(super) unsafe fn init_non_primary() {
    // No additional initialization needed for non-primary CPUs
}
