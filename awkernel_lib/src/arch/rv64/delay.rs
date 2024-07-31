use crate::delay::Delay;

// we should get this info from device tree
const ACLINT_MTIME_BASE: u32 = 0x0200_0000 + 0x0000bff8;
const RISCV_TIMEBASE_FREQ: u64 = 10_000_000;

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
        // as microsec
        unsafe {
            let mtime = ACLINT_MTIME_BASE as *const u64;
            *mtime * 1_000_000 / RISCV_TIMEBASE_FREQ
        }
    }

    fn cpu_counter() -> u64 {
        let cycle: u64;
        unsafe {
            core::arch::asm!("rdcycle {}", out(reg) cycle);
        }
        cycle
    }
}
