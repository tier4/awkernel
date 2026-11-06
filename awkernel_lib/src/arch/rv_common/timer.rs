//! Timer driven by the CLINT machine timer interrupt.

use super::interrupt_controller::{clint, TIMER_IRQ};
use core::time::Duration;

/// Per-hart timer using the CLINT `mtimecmp` registers.
pub struct ClintTimer;

impl crate::timer::Timer for ClintTimer {
    #[inline]
    fn reset(&self, dur: Duration) {
        clint().set_timer(dur);
    }

    #[inline]
    fn irq_id(&self) -> u16 {
        TIMER_IRQ
    }

    #[inline]
    fn disable(&self) {
        clint().clear_timer();
    }
}
