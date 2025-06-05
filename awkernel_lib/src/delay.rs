//! `delay` provides `Delay` trait to represent architecture specific delay functions.
//! Users can call the delay functions transparently by calling functions defined this module.

use crate::arch::ArchImpl;

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
        assert!(sec < u64::MAX / 1_000_000);
        Self::wait_microsec(sec * 1000 * 1000);
    }

    /// This function returns uptime in microseconds.
    fn uptime() -> u64;

    /// This function returns uptime in nanoseconds.
    fn uptime_nano() -> u128;

    /// Return CPU cycle counter.
    fn cpu_counter() -> u64;

    /// Pause a CPU during busy loop to reduce CPU power consumption.
    fn pause() {
        core::hint::spin_loop();
    }
}

/// Wait interrupt.
#[inline(always)]
pub fn wait_interrupt() {
    ArchImpl::wait_interrupt();
}

/// Wait microseconds.
///
/// # Example
///
/// ```
/// awkernel_lib::delay::wait_microsec(10); // Wait 10 microseconds.
/// ```
#[inline(always)]
pub fn wait_microsec(usec: u64) {
    ArchImpl::wait_microsec(usec);
}

/// Wait milliseconds.
///
/// # Example
///
/// ```
/// awkernel_lib::delay::wait_millisec(10); // Wait 10 milliseconds.
/// ```
#[inline(always)]
pub fn wait_millisec(msec: u64) {
    ArchImpl::wait_millisec(msec);
}

/// Wait seconds.
///
/// # Example
///
/// ```
/// awkernel_lib::delay::wait_sec(1); // Wait 1 seconds.
/// ```
#[inline(always)]
pub fn wait_sec(sec: u64) {
    ArchImpl::wait_sec(sec);
}

/// Never return.
pub fn wait_forever() -> ! {
    ArchImpl::wait_forever()
}

/// Return uptime in microseconds.
/// Note that this function may not monotonically increase.
///
/// # Example
///
/// ```
/// use awkernel_lib::delay::uptime;
/// let start = uptime();
/// let end = uptime();
/// log::info!("{} [us]", end - start);
/// ```
#[inline(always)]
pub fn uptime() -> u64 {
    ArchImpl::uptime()
}

/// Return uptime in nanoseconds.
/// Note that this function may not monotonically increase.
///
/// # Example
///
/// ```
/// use awkernel_lib::delay::uptime_nano;
/// let start = uptime_nano();
/// let end = uptime_nano();
/// log::info!("{} [ns]", end - start);
/// ```
#[inline(always)]
pub fn uptime_nano() -> u128 {
    ArchImpl::uptime_nano()
}

/// Pause a CPU during busy loop to reduce CPU power consumption.
///
/// # Example
///
/// ```
/// awkernel_lib::delay::pause();
/// ```
#[inline(always)]
pub fn pause() {
    ArchImpl::pause();
}

/// Return CPU cycle counter.
///
/// # Example
///
/// ```
/// use awkernel_lib::delay::cpu_counter;
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
#[inline(always)]
pub fn cpu_counter() -> u64 {
    ArchImpl::cpu_counter()
}
