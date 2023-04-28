//! Disable interrupts.

use crate::arch::ArchInterrupt;

pub trait Interrupt {
    /// Get current interrupt flag(s).
    fn get_flag() -> usize;

    /// Disable interrupt.
    fn disable();

    /// Set interrupt flag(s).
    fn set_flag(flag: usize);
}

/// Save, disable, restore interrupt flag(s).
///
/// ```
/// use awkernel_lib::interrupt::InterruptGuard;
///
/// fn require_interrupt_disable() {
///     let int_guard = InterruptGuard::new(); // Save current interrupt flags and disable interrupts.
///     // Interrupts are disabled here,
///     // and interrupt flag(s) are automatically restored after this function.
/// }
/// ```
pub struct InterruptGuard {
    flag: usize,
}

impl InterruptGuard {
    pub fn new() -> Self {
        let flag = ArchInterrupt::get_flag();
        ArchInterrupt::disable();

        Self { flag }
    }
}

impl Drop for InterruptGuard {
    fn drop(&mut self) {
        ArchInterrupt::set_flag(self.flag);
    }
}
