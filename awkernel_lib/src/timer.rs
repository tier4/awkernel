use core::sync::atomic::AtomicBool;

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

use crate::sync::{mcs::MCSNode, mutex::Mutex};

static TIMER: Mutex<Option<Box<dyn Timer + Send + Sync>>> = Mutex::new(None);
static IS_TIMER_ENABLED: AtomicBool = AtomicBool::new(false);

pub trait Timer {
    /// Reset the timer interrupt.
    fn reset(&self);

    /// Get IRQ#.
    fn irq_id(&self) -> u16;

    /// Disable the timer interrupt.
    fn disable(&self);
}

pub fn register_timer(timer: Box<dyn Timer + Send + Sync>) {
    IS_TIMER_ENABLED.store(true, core::sync::atomic::Ordering::Relaxed);
    let mut node = MCSNode::new();
    let mut guard = TIMER.lock(&mut node);
    *guard = Some(timer);
}

/// Re-enable timer.
#[inline(always)]
pub fn reset() {
    let mut node = MCSNode::new();
    let guard = TIMER.lock(&mut node);
    if let Some(timer) = guard.as_ref() {
        timer.reset()
    }
}

/// Get IRQ#.
#[inline(always)]
pub fn irq_id() -> Option<u16> {
    let mut node = MCSNode::new();
    let guard = TIMER.lock(&mut node);

    guard.as_ref().map(|timer| timer.irq_id())
}

/// Disable the timer interrupt.
#[inline(always)]
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
        log::info!("timer::TIMER is not yet initialized.");
    } else {
        log::info!("timer::TIMER has been initialized.");
    }
}

#[inline(always)]
pub fn is_timer_enabled() -> bool {
    IS_TIMER_ENABLED.load(core::sync::atomic::Ordering::Relaxed)
}
