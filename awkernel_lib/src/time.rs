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
    ops::{Add, AddAssign, Sub, SubAssign},
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

    pub fn saturating_duration_since(&self, earlier: Self) -> Duration {
        if self.uptime > earlier.uptime {
            Duration::from_nanos(
                ((self.uptime.saturating_sub(earlier.uptime)).min(u64::MAX as u128)) as u64,
            )
        } else {
            Duration::new(0, 0)
        }
    }

    /// If the `duration` is greater than the uptime, return `None`.
    /// Otherwise, return the past time after subtracting the `duration` from the uptime.
    pub fn checked_sub(&self, duration: Duration) -> Option<Time> {
        self.uptime
            .checked_sub(duration.as_nanos())
            .map(|uptime| Time { uptime })
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

impl Sub<Duration> for Time {
    type Output = Time;

    /// Returns a past time after subtracting the `duration` from the uptime.
    ///
    /// # Panics
    ///
    /// If the `duration` is greater than the uptime, this function will panic.
    fn sub(self, other: Duration) -> Self {
        self.checked_sub(other)
            .expect("overflow when subtracting duration from instant")
    }
}

impl SubAssign<Duration> for Time {
    fn sub_assign(&mut self, other: Duration) {
        *self = *self - other;
    }
}

impl Sub<Time> for Time {
    type Output = Duration;

    fn sub(self, other: Time) -> Duration {
        self.saturating_duration_since(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_time_add_sub() {
        let dur1 = Duration::from_secs(1);
        let dur2 = Duration::from_secs(2);

        assert_eq!(dur1 + dur2, Duration::from_secs(3));
        assert_eq!(dur2 - dur1, dur1);

        let earlier = Time::zero();
        let middle = earlier + dur1;
        let later = middle + dur2;

        assert_eq!(later - middle, dur2);
        assert_eq!(middle - earlier, dur1);
        assert_eq!(later - earlier, dur1 + dur2);

        assert_eq!(earlier - middle, Duration::ZERO);
        assert_eq!(middle - later, Duration::ZERO);
        assert_eq!(earlier - later, Duration::ZERO);
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting durations")]
    fn test_duration_sub_overflow() {
        let dur1 = Duration::from_secs(1);
        let dur2 = Duration::from_secs(2);
        let _ = dur1 - dur2;
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from instant")]
    fn test_time_sub_overflow() {
        let earlier = Time::zero();
        let dur = Duration::from_secs(1);
        let _ = earlier - dur;
    }
}
