//! # armv8-timer
//!
//! ## `CNTPCT_EL0`: Counter-timer Physical Count register
//!
//! Holds the 64-bit physical count value.
//!
//! ## `CNTP_CTL_EL0`: Counter-timer Physical Timer Control register
//!
//! - 0bABC
//!   - A: Interrupt Status
//!   - B: Interrupt Mask
//!   - C: Enable
//!
//! ## `CNTFRQ_EL0`: Counter-timer Frequency register
//!
//! Indicates the system counter clock frequency, in Hz.
//!
//! ## `CNTP_CVAL_EL0`: Counter-timer Physical Timer CompareValue Register
//!
//! The comparator register, CVAL, is a 64-bit register. Software writes a value to this register and the timer triggers when the
//! count reaches, or exceeds, that value, as you can see here:
//!
//! ```plain
//! Timer Condition Met: CVAL <= System Count
//! ```
//!
//! ## `CNTP_TVAL_EL0`:  Counter-timer Physical Timer TimerValue register
//!
//! The timer register, TVAL, is a 32-bit register. When software writes TVAL, the processor reads the current system count
//! internally, adds the written value, and then populates CVAL:
//!
//! ```plain
//! CVAL = TVAL + System Counter
//! Timer Condition Met: CVAL <= System Count
//! ```
//!
//! Reading TVAL back will show it decrementing down to 0, while the system count increments. TVAL reports a signed value, and
//! will continue to decrement after the timer fires, which allows software to determine how long ago the timer fired.
//!
//! ## Interrupt Number
//!
//! The interrupt ID (INTID) that is used for each timer is defined by the Server Base System Architecture (SBSA).
//!
//! EL1 Physical Timer (CNTP)'s #IRQ is 30.

pub struct Armv8Timer {
    irq: u16,
}

impl Armv8Timer {
    pub const fn new(irq: u16) -> Self {
        Armv8Timer { irq }
    }
}

impl crate::timer::Timer for Armv8Timer {
    fn reset(&self) {
        // every 1/2^19 = .000_001_9 [s].
        let t = awkernel_aarch64::cntfrq_el0::get() >> 19;
        unsafe {
            awkernel_aarch64::cntp_tval_el0::set(t);
            awkernel_aarch64::cntp_ctl_el0::set(1); // Enable interrupt.
        }
    }

    fn irq_id(&self) -> u16 {
        self.irq
    }

    fn disable(&self) {
        unsafe { awkernel_aarch64::cntp_ctl_el0::set(0) };
    }
}
