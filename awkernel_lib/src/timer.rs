use crate::sync::{mcs::MCSNode, mutex::Mutex};

static TIMER: Mutex<Option<&'static (dyn Timer + Sync + Send)>> = Mutex::new(None);

pub trait Timer {
    /// Reset the timer interrupt.
    fn reset(&self);

    /// Get IRQ#.
    fn irq_id(&self) -> u16;

    /// Disable the timer interrupt.
    fn disable(&self);
}

pub fn register_timer(timer: &'static (dyn Timer + Sync + Send)) {
    let mut node = MCSNode::new();
    let mut guard = TIMER.lock(&mut node);
    *guard = Some(timer);
}

/// Re-enable timer.
pub fn reset() {
    let mut node = MCSNode::new();
    let guard = TIMER.lock(&mut node);
    if let Some(timer) = guard.as_ref() {
        timer.reset()
    }
}

/// Get IRQ#.
pub fn irq_id() -> Option<u16> {
    let mut node = MCSNode::new();
    let guard = TIMER.lock(&mut node);

    guard.as_ref().map(|timer| timer.irq_id())
}

/// Disable the timer interrupt.
pub fn disable() {
    let mut node = MCSNode::new();
    let guard = TIMER.lock(&mut node);
    if let Some(timer) = guard.as_ref() {
        timer.disable()
    }
}

pub fn sanity_check() {
    let mut node = MCSNode::new();
    let guard = TIMER.lock(&mut node);

    if guard.is_none() {
        log::warn!("timer::TIMER is not yet initialized.");
    } else {
        log::info!("timer::TIMER has been initialized.");
    }
}
