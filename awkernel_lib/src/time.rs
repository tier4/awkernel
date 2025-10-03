/// Time module.
///
/// This module provides a time struct that can be used to measure time.
///
/// # Example
///
/// ```
/// use awkernel_lib::time::Time;
///
/// let time = Time::now();
/// log::info!("Uptime: {} [ms]", time.uptime().as_millis());
/// ```
///
/// ```
/// use awkernel_lib::time::Time;
///
/// let time = Time::now();
/// for _ in 0..10 {
///    // Do something
/// }
/// let diff = time.elapsed();
///
/// log::info!("Elapsed: {} [ms]", diff.as_millis());
/// ```
use core::{
    ops::{Add, AddAssign},
    time::Duration,
};

/// Monotonically increasing time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Time {
    uptime: u128,
}

impl Time {
    #[inline]
    pub fn now() -> Self {
        Self {
            uptime: crate::delay::uptime_nano(),
        }
    }

    #[inline]
    pub const fn zero() -> Self {
        Self { uptime: 0 }
    }

    /// Return uptime.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_lib::time::Time;
    ///
    /// let time = Time::now();
    /// log::info!("Uptime: {} [ms]", time.uptime().as_millis());
    /// ```
    #[inline]
    pub fn uptime(&self) -> Duration {
        Duration::from_nanos(self.uptime as u64)
    }

    /// Return elapsed time from the uptime.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_lib::time::Time;
    ///
    /// let time = Time::now();
    /// for _ in 0..10 {
    ///     // Do something
    /// }
    /// let diff = time.elapsed();
    ///
    /// log::info!("Elapsed: {} [ms]", diff.as_millis());
    /// ```
    #[inline]
    pub fn elapsed(&self) -> Duration {
        let now = crate::delay::uptime_nano();

        // Because `uptime_nano` is not monotonically increasing,
        // we need to check the time.
        if now > self.uptime {
            Duration::from_nanos((now - self.uptime) as u64)
        } else {
            Duration::from_nanos(0)
        }
    }

    /// Converts uptime (in nanoseconds) to milliseconds.
    pub fn as_millis(&self) -> u128 {
        self.uptime / 1_000_000
    }

    pub fn saturating_duration_since(&self, earlier: Self) -> Duration {
        if self.uptime > earlier.uptime {
            Duration::from_nanos(
                ((self.uptime.saturating_sub(earlier.uptime)).min(u64::MAX as u128)) as u64,
            )
        } else {
            Duration::new(0, 0)
        }
    }
}

impl Add<Duration> for Time {
    type Output = Self;

    fn add(self, dur: Duration) -> Self {
        Self {
            uptime: self.uptime + dur.as_nanos(),
        }
    }
}

impl AddAssign<Duration> for Time {
    fn add_assign(&mut self, dur: Duration) {
        self.uptime += dur.as_nanos();
    }
}
