use array_macro::array;
use core::{sync::atomic::AtomicBool, time::Duration};

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

use crate::{
    cpu::NUM_MAX_CPU,
    sync::{mcs::MCSNode, mutex::Mutex},
    time::Instant,
};

static TIMER: Mutex<Option<Box<dyn Timer + Send + Sync>>> = Mutex::new(None);
static IS_TIMER_ENABLED: AtomicBool = AtomicBool::new(false);

pub trait Timer {
    /// Reset the timer interrupt.
    fn reset(&self, dur: Duration);

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
///
/// # x86_64
///
/// Because x86 APIC timer is edge-triggered, we set the timer to periodic
/// to avoid lost timer interrupts.
///
/// # AArch64
///
/// AArch64's timer is level-sensitive and it is not periodic.
#[inline(always)]
pub fn reset(dur: Duration) {
    let mut node = MCSNode::new();
    let guard = TIMER.lock(&mut node);
    if let Some(timer) = guard.as_ref() {
        timer.reset(dur)
    }
}

/// Arm the timer for an absolute future `deadline` instead of a relative
/// duration. Layered trivially on top of [`reset`] (`deadline -
/// Instant::now()`); whether this actually achieves exact one-shot precision
/// depends on the underlying driver (see [`TimerRequestId`]'s own doc for
/// why a raw call to this alone isn't enough when more than one logical
/// consumer shares the single per-core timer).
#[inline(always)]
pub fn arm_at(deadline: Instant) {
    reset(deadline.saturating_duration_since(Instant::now()));
}

/// Get IRQ#.
#[inline(always)]
pub fn irq_id() -> Option<u16> {
    let mut node = MCSNode::new();
    let guard = TIMER.lock(&mut node);
    guard.as_ref().as_ref().map(|timer| timer.irq_id())
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

// ---------------------------------------------------------------------------
// Per-core timer request multiplexer.
//
// There is exactly one physical timer resource per core (see `reset`'s own
// doc: on x86_64 it is forced into periodic mode specifically as a safety
// net against a lost edge-triggered interrupt). A second, independent
// logical consumer that wants its own precise, arbitrary-future-timestamp
// deadline (DAG-Fluid's own Deadline-Partition boundary detection) cannot
// just call `reset`/`arm_at` directly -- it would stomp on whatever
// `awkernel_lib::cpu::sleep_cpu_no_std`'s own idle-wakeup deadline had
// armed, since both would be fighting over the same single register block.
//
// This multiplexer merges every registered consumer's own "please wake me
// at time X" request per core into one soonest-wins arm of the physical
// timer, and re-arms for whatever remains every time it fires.
// ---------------------------------------------------------------------------

/// A logical consumer of the single per-core timer resource.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimerRequestId {
    /// `awkernel_lib::cpu::sleep_cpu_no_std`'s own idle-CPU wakeup deadman.
    IdleWakeup,
    /// Reserved for DAG-Fluid's own system-wide Deadline-Partition boundary
    /// detection. Unused until that work registers a callback for it via
    /// [`register_timer_callback`] and starts calling [`request_at`] --
    /// firing this request today is a silent no-op (see
    /// [`invoke_callback`]).
    DpBoundary,
}

const NUM_TIMER_REQUESTS: usize = 2;

impl TimerRequestId {
    const ALL: [TimerRequestId; NUM_TIMER_REQUESTS] =
        [TimerRequestId::IdleWakeup, TimerRequestId::DpBoundary];

    const fn index(self) -> usize {
        match self {
            TimerRequestId::IdleWakeup => 0,
            TimerRequestId::DpBoundary => 1,
        }
    }
}

#[derive(Clone, Copy)]
struct PerCpuTimerState {
    pending: [Option<Instant>; NUM_TIMER_REQUESTS],
}

impl PerCpuTimerState {
    const fn new() -> Self {
        Self {
            pending: [None; NUM_TIMER_REQUESTS],
        }
    }

    fn set(&mut self, id: TimerRequestId, deadline: Instant) {
        self.pending[id.index()] = Some(deadline);
    }

    fn clear(&mut self, id: TimerRequestId) {
        self.pending[id.index()] = None;
    }

    /// The earliest still-pending deadline across every request, if any.
    fn soonest(&self) -> Option<Instant> {
        self.pending.iter().filter_map(|d| *d).min()
    }
}

static TIMER_REQUESTS: [Mutex<PerCpuTimerState>; NUM_MAX_CPU] =
    array![_ => Mutex::new(PerCpuTimerState::new()); NUM_MAX_CPU];

// `&'static` rather than an owned `Box` specifically so `invoke_callback` can
// *copy* the reference out of the lock (`Option<&'static dyn Fn() + ...>` is
// `Copy`, unlike `Option<Box<dyn Fn() + ...>>`) and drop the guard *before*
// calling it. Callbacks are registered once at boot and never unregistered,
// so leaking them in `register_timer_callback` below is intentional and
// permanent, not a growing leak.
static TIMER_CALLBACKS: [Mutex<Option<&'static (dyn Fn() + Send + Sync)>>; NUM_TIMER_REQUESTS] =
    [Mutex::new(None), Mutex::new(None)];

/// Register the callback invoked (on whichever CPU it happens to fire on)
/// when `id`'s deadline is reached. Overwrites any previously registered
/// callback for `id`. The callback runs with no locks held on this
/// module's own state, so it may safely call [`request_at`]/[`cancel`]
/// again (e.g. to re-arm itself for a further-future deadline, the same
/// way the pre-multiplexer idle-wakeup timer callback always did) --
/// including, transitively, a re-entrant call back into *this same
/// callback* (see [`invoke_callback`]'s own doc for why that used to
/// deadlock).
pub fn register_timer_callback(id: TimerRequestId, callback: Box<dyn Fn() + Send + Sync>) {
    let callback: &'static (dyn Fn() + Send + Sync) = Box::leak(callback);
    let mut node = MCSNode::new();
    let mut guard = TIMER_CALLBACKS[id.index()].lock(&mut node);
    *guard = Some(callback);
}

/// Invoke `id`'s registered callback, if any, with `TIMER_CALLBACKS[id]`'s
/// own lock *not* held. This matters: [`arm_and_recheck`] can recurse back
/// into [`handle_timer_fire`] -> `invoke_callback` for the very same `id`
/// on the very same call stack (e.g. a callback that re-`request_at`s a
/// deadline that's already passed by the time the hardware write
/// completes). `TIMER_CALLBACKS`'s lock is a plain non-reentrant spinlock
/// (see `awkernel_sync::mcs`), so calling `callback()` while still holding
/// it would self-deadlock the very first time that recursion happens --
/// confirmed the hard way as this module's first real boot hang, with
/// interrupts hardware-disabled for the whole spin (the timer ISR itself
/// is entered through an x86 interrupt gate), freezing the core
/// permanently rather than just missing one tick.
fn invoke_callback(id: TimerRequestId) {
    let callback = {
        let mut node = MCSNode::new();
        let guard = TIMER_CALLBACKS[id.index()].lock(&mut node);
        *guard
    };
    if let Some(callback) = callback {
        callback();
    }
}

/// Arm the physical timer for `deadline`, then immediately recheck whether
/// it has already passed -- the risk `fully_one_shot_timer` trades periodic
/// mode's lost-edge safety net away for (see this module's own doc). If so,
/// fire synchronously right here instead of waiting for an interrupt that
/// may never come. This mirrors
/// `awkernel_lib::cpu::sleep_cpu_no_std::sleep`'s own pre-existing
/// elapsed-time recheck immediately before committing to halt, for exactly
/// the same reason (edge-triggered interrupts arriving while interrupts
/// are masked are lost).
///
/// Every caller of `arm_at` in this module (there is no other) goes through
/// here rather than calling it directly, specifically so this recheck can
/// never be forgotten at a new call site the way it originally was at two
/// of this function's own three call sites.
fn arm_and_recheck(deadline: Instant) {
    arm_at(deadline);
    if Instant::now() >= deadline {
        handle_timer_fire();
    }
}

/// Request (or update) a deadline for `id` on the calling CPU. If `id`'s
/// new deadline is now the soonest pending deadline on this CPU, arms the
/// physical timer for it (see [`arm_and_recheck`]).
pub fn request_at(id: TimerRequestId, deadline: Instant) {
    let cpu = crate::cpu::cpu_id();

    let is_new_soonest = {
        let mut node = MCSNode::new();
        let mut state = TIMER_REQUESTS[cpu].lock(&mut node);
        state.set(id, deadline);
        matches!(state.soonest(), Some(soonest) if soonest == deadline)
    };

    if is_new_soonest {
        arm_and_recheck(deadline);
    }
}

/// Cancel a pending request for `id` on the calling CPU. Re-arms for the
/// next-soonest remaining request, or disables the timer if none remain.
pub fn cancel(id: TimerRequestId) {
    let cpu = crate::cpu::cpu_id();

    // Read the lock's result and drop the guard *before* arming: `arm_and_recheck`
    // can recurse into `handle_timer_fire`, which re-locks this same
    // per-CPU mutex -- holding it here would deadlock.
    let next = {
        let mut node = MCSNode::new();
        let mut state = TIMER_REQUESTS[cpu].lock(&mut node);
        state.clear(id);
        state.soonest()
    };

    match next {
        Some(next) => arm_and_recheck(next),
        None => disable(),
    }
}

/// Called from the timer IRQ handler: fire every pending request on the
/// calling CPU whose deadline has been reached (invoking each one's
/// registered callback, if any), then re-arm for whatever remains. Safe to
/// call even if nothing has actually reached its deadline yet (a no-op
/// re-arm in that case).
pub fn handle_timer_fire() {
    let cpu = crate::cpu::cpu_id();
    let now = Instant::now();

    for id in TimerRequestId::ALL {
        let fired = {
            let mut node = MCSNode::new();
            let mut state = TIMER_REQUESTS[cpu].lock(&mut node);
            match state.pending[id.index()] {
                Some(deadline) if deadline <= now => {
                    state.clear(id);
                    true
                }
                _ => false,
            }
        };
        // Invoke the callback with no lock held: it may call
        // `request_at`/`cancel` itself (e.g. to re-arm), which would
        // deadlock against a still-held `TIMER_REQUESTS[cpu]` lock.
        if fired {
            invoke_callback(id);
        }
    }

    // Same reasoning as `cancel`: drop the lock before arming, since
    // `arm_and_recheck` may recurse back into this very function.
    let next = {
        let mut node = MCSNode::new();
        let state = TIMER_REQUESTS[cpu].lock(&mut node);
        state.soonest()
    };

    match next {
        Some(next) => arm_and_recheck(next),
        None => disable(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_per_cpu_timer_state_soonest_is_none_when_empty() {
        let state = PerCpuTimerState::new();
        assert_eq!(state.soonest(), None);
    }

    #[test]
    fn test_per_cpu_timer_state_soonest_picks_the_minimum() {
        let mut state = PerCpuTimerState::new();
        let t10 = Instant::zero() + Duration::from_millis(10);
        let t5 = Instant::zero() + Duration::from_millis(5);
        state.set(TimerRequestId::IdleWakeup, t10);
        state.set(TimerRequestId::DpBoundary, t5);
        assert_eq!(state.soonest(), Some(t5));
    }

    #[test]
    fn test_per_cpu_timer_state_clear_falls_back_to_remaining() {
        let mut state = PerCpuTimerState::new();
        let t10 = Instant::zero() + Duration::from_millis(10);
        let t5 = Instant::zero() + Duration::from_millis(5);
        state.set(TimerRequestId::IdleWakeup, t10);
        state.set(TimerRequestId::DpBoundary, t5);
        state.clear(TimerRequestId::DpBoundary);
        assert_eq!(state.soonest(), Some(t10));
    }

    #[test]
    fn test_per_cpu_timer_state_clear_last_one_is_none() {
        let mut state = PerCpuTimerState::new();
        let t5 = Instant::zero() + Duration::from_millis(5);
        state.set(TimerRequestId::IdleWakeup, t5);
        state.clear(TimerRequestId::IdleWakeup);
        assert_eq!(state.soonest(), None);
    }

    #[test]
    fn test_per_cpu_timer_state_updating_same_id_replaces_its_own_deadline() {
        let mut state = PerCpuTimerState::new();
        let t10 = Instant::zero() + Duration::from_millis(10);
        let t20 = Instant::zero() + Duration::from_millis(20);
        state.set(TimerRequestId::IdleWakeup, t10);
        state.set(TimerRequestId::IdleWakeup, t20);
        assert_eq!(state.soonest(), Some(t20));
    }
}
