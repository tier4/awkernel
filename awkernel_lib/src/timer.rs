use core::ptr::write_volatile;

static mut TIMER: Option<&'static dyn Timer> = None;

pub trait Timer {
    /// Reset the timer interrupt.
    fn reset(&self);

    /// Get IRQ#.
    fn irq_id(&self) -> u16;

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
pub fn irq_id() -> Option<u16> {
    unsafe { TIMER }.map(|timer| timer.irq_id())
}

/// Disable the timer interrupt.
pub fn disable() {
    if let Some(timer) = unsafe { TIMER } {
        timer.disable()
    }
}

pub fn sanity_check() {
    if unsafe { TIMER.is_none() } {
        log::warn!("timer::TIMER is not yet initialized.");
    } else {
        log::info!("timer::TIMER has been initialized.");
    }
}
