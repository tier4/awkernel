//! - `CNTPCT_EL0`: Counter-timer Physical Count register
//!   - Holds the 64-bit physical count value.
//! - `CNTP_CTL_EL0`: Counter-timer Physical Timer Control register
//!   - 0bABC
//!     - A: Interrupt Status
//!     - B: Interrupt Mask
//!     - C: Enable
//! - `CNTFRQ_EL0`: Counter-timer Frequency register
//!   - Indicates the system counter clock frequency, in Hz.
//! - `CNTP_TVAL_EL0`:  Counter-timer Physical Timer TimerValue register
//!   - Holds the timer value for the EL1 physical timer.
//! - `CNTP_CVAL_EL0`: Counter-timer Physical Timer CompareValue Register

pub struct ArmTimer {
    irq: usize,
}

impl ArmTimer {
    pub const fn new(irq: usize) -> Self {
        ArmTimer { irq }
    }
}

impl crate::timer::Timer for ArmTimer {
    fn reset(&self) {
        // every 1/(2^20) = 0.000_000_954 [s].
        let t = awkernel_aarch64::cntfrq_el0::get() >> 20;
        unsafe {
            awkernel_aarch64::cntp_tval_el0::set(t);
            awkernel_aarch64::cntp_ctl_el0::set(1); // Enable interrupt.
        }
    }

    fn irq_id(&self) -> usize {
        self.irq
    }

    fn disable(&self) {
        unsafe { awkernel_aarch64::cntp_ctl_el0::set(0) };
    }
}
