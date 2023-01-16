//! `delay` provides `Delay` trait to represent architecture specific delay functions.
//! Users can call the delay functions transparently by calling functions defined this module.

use crate::arch::ArchDelay;

/// Trait for architecture specific delay functions.
impl ArchDelay where ArchDelay: Delay {}

pub trait Delay {
    /// Wait interrupt.
    fn wait_interrupt();

    /// Wait microseconds.
    fn wait_microsec(usec: u64);

    /// Never return.
    fn wait_forever() -> ! {
        loop {
            Self::wait_interrupt();
        }
    }

    /// Wait milliseconds.
    fn wait_millisec(msec: u64) {
        assert!(msec < u64::MAX / 1000);
        Self::wait_microsec(msec * 1000);
    }

    /// Wait seconds.
    fn wait_sec(sec: u64) {
        assert!(sec < u64::MAX / 1000_000);
        Self::wait_microsec(sec * 1000 * 1000);
    }

    /// This function returns uptime in microseconds.
    fn uptime() -> u64;

    /// Return CPU cycle counter.
    fn cpu_counter() -> u64;

    /// Pause a CPU during busy loop to reduce CPU power consumption.
    fn pause() {
        core::hint::spin_loop();
    }
}

/// Wait interrupt.
pub fn wait_interrupt() {
    ArchDelay::wait_interrupt();
}

/// Wait microseconds.
///
/// # Example
///
/// ```
/// t4os_lib::delay::wait_microsec(10); // Wait 10 microseconds.
/// ```
pub fn wait_microsec(usec: u64) {
    ArchDelay::wait_microsec(usec);
}

/// Wait milliseconds.
///
/// # Example
///
/// ```
/// t4os_lib::delay::wait_millisec(10); // Wait 10 milliseconds.
/// ```
pub fn wait_millisec(msec: u64) {
    ArchDelay::wait_millisec(msec);
}

/// Wait seconds.
///
/// # Example
///
/// ```
/// t4os_lib::delay::wait_sec(1); // Wait 1 seconds.
/// ```
pub fn wait_sec(sec: u64) {
    ArchDelay::wait_sec(sec);
}

/// Never return.
pub fn wait_forever() -> ! {
    ArchDelay::wait_forever()
}

/// Return uptime in microseconds.
///
/// # Example
///
/// ```
/// use t4os_lib::delay::uptime;
/// let start = uptime();
/// let end = uptime();
/// log::info!("{} [us]", end - start);
/// ```
pub fn uptime() -> u64 {
    ArchDelay::uptime()
}

/// Pause a CPU during busy loop to reduce CPU power consumption.
///
/// # Example
///
/// ```
/// t4os_lib::delay::pause();
/// ```
pub fn pause() {
    ArchDelay::pause();
}

/// Return CPU cycle counter.
///
/// # Example
///
/// ```
/// use t4os_lib::delay::cpu_counter;
///
/// // Wait 150 CPU cycles.
/// let start = cpu_counter();
/// loop {
///     let counter = cpu_counter();
///     if counter - start >= 150 {
///         break;
///     }
/// }
/// ```
pub fn cpu_counter() -> u64 {
    ArchDelay::cpu_counter()
}
