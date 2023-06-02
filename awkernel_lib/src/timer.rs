use core::ptr::write_volatile;

static mut TIMER: Option<&'static dyn Timer> = None;

pub trait Timer {
    /// Reset the timer interrupt.
    fn reset(&self);

    /// Get IRQ#.
    fn irq_id(&self) -> usize;

    /// Disable the timer interrupt.
    fn disable(&self);
}

pub fn register_timer(timer: &'static dyn Timer) {
    unsafe { write_volatile(&mut TIMER, Some(timer)) };
}

/// Re-enable timer.
pub fn reset() {
    if let Some(timer) = unsafe { TIMER } {
        timer.reset()
    }
}

/// Get IRQ#.
pub fn irq_id() -> Option<usize> {
    if let Some(timer) = unsafe { TIMER } {
        Some(timer.irq_id())
    } else {
        None
    }
}

/// Disable the timer interrupt.
pub fn disable() {
    if let Some(timer) = unsafe { TIMER } {
        timer.disable()
    }
}
