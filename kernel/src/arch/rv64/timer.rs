use core::ptr::{read_volatile, write_volatile};
use core::time::Duration;

/// RISC-V Timer Implementation
/// Uses MTIME (machine time) and MTIMECMP (machine time compare) registers
pub struct RiscvTimer {
    irq: u16,
}

// RISC-V timer memory-mapped register addresses
// These should match the device tree or platform configuration
const ACLINT_MTIME_BASE: usize = 0x0200_0000 + 0x0000bff8;
const ACLINT_MTIMECMP_BASE: usize = 0x0200_0000 + 0x00004000;
const RISCV_TIMEBASE_FREQ: u64 = 10_000_000; // 10 MHz

impl RiscvTimer {
    pub const fn new(irq: u16) -> Self {
        RiscvTimer { irq }
    }

    /// Get the current machine time
    fn get_mtime() -> u64 {
        let mtime = ACLINT_MTIME_BASE as *const u64;
        unsafe { read_volatile(mtime) }
    }

    /// Get the current hart ID
    fn get_hart_id() -> usize {
        let hart_id: usize;
        unsafe {
            core::arch::asm!("csrr {}, mhartid", out(reg) hart_id);
        }
        hart_id
    }

    /// Set the machine time compare value
    fn set_mtimecmp(&self, value: u64) {
        // Each hart has its own MTIMECMP register at ACLINT_MTIMECMP_BASE + (hartid * 8)
        let hart_id = Self::get_hart_id();
        let mtimecmp = (ACLINT_MTIMECMP_BASE + (hart_id * 8)) as *mut u64;
        unsafe { write_volatile(mtimecmp, value) };
    }

    /// Enable machine timer interrupt
    fn enable_mti(&self) {
        unsafe {
            // Set MIE.MTIE (Machine Timer Interrupt Enable) bit
            core::arch::asm!("csrrs t0, mie, {}", in(reg) 1 << 7);
        }
    }

    /// Disable machine timer interrupt
    fn disable_mti(&self) {
        unsafe {
            // Clear MIE.MTIE (Machine Timer Interrupt Enable) bit
            core::arch::asm!("csrrc t0, mie, {}", in(reg) 1 << 7);
        }
    }
}

impl awkernel_lib::timer::Timer for RiscvTimer {
    fn reset(&self, dur: Duration) {
        let current_time = Self::get_mtime();
        let ticks = (dur.as_nanos() as u64 * RISCV_TIMEBASE_FREQ) / 1_000_000_000;
        let target_time = current_time.saturating_add(ticks);

        // Set the compare value
        self.set_mtimecmp(target_time);

        // Enable machine timer interrupt
        self.enable_mti();
    }

    fn irq_id(&self) -> u16 {
        self.irq
    }

    fn disable(&self) {
        // Disable machine timer interrupt
        self.disable_mti();

        // Set MTIMECMP to maximum value to prevent spurious interrupts
        self.set_mtimecmp(u64::MAX);
    }
}
