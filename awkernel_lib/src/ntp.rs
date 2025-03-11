use crate::arch::ArchImpl;
use core::{
    fmt::Debug,
    ops::{Add, Sub},
    time::Duration,
};

/// Module for NTP and system clock.
///
/// This module provides the interface for NTP daemons and managing the system clock.
#[derive(Copy, Clone)]
pub struct SystemTime {
    /// Nanoseconds since UNIX epoch.
    nsecs: u128,
}

impl SystemTime {
    pub fn new(nsecs: u128) -> Self {
        SystemTime { nsecs }
    }

    pub fn now() -> Self {
        ArchImpl::get_time()
    }

    pub const fn epoch() -> Self {
        SystemTime { nsecs: 0 }
    }

    pub fn duration_since(&self, other: Self) -> Result<Duration, ()> {
        Ok(Duration::from_secs(1))
    }
}

impl Debug for SystemTime {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "SystemTime({} [ns] since epoch)", self.nsecs)
    }
}

impl Add<Duration> for SystemTime {
    type Output = Self;

    fn add(self, dur: Duration) -> Self {
        SystemTime {
            nsecs: self.nsecs + dur.as_nanos() as u128,
        }
    }
}

impl Sub<Duration> for SystemTime {
    type Output = Self;

    fn sub(self, dur: Duration) -> Self {
        SystemTime {
            nsecs: self.nsecs - dur.as_nanos() as u128,
        }
    }
}

pub trait Ntp {
    /// Get the current time in nanoseconds.
    fn get_time() -> SystemTime;

    fn set_time(new: u64);

    fn sync_time();
}
