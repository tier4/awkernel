use alloc::string::String;
use alloc::{format, string::ToString};

use crate::arch::ArchImpl;
use core::{
    fmt::Debug,
    ops::{Add, Sub},
    time::Duration,
};

pub mod packet;
pub mod timestamp;

/// Represents the system time.
/// TODO: could be merged with time.rs?
#[derive(Copy, Clone)]
pub struct SystemTime {
    /// Nanoseconds since UNIX epoch.
    nsecs: u128,
}
impl SystemTime {
    pub fn new(nsecs: u128) -> Self {
        Self { nsecs }
    }

    pub const fn epoch() -> Self {
        Self { nsecs: 0 }
    }

    pub fn duration_since(&self, other: Self) -> Result<Duration, ()> {
        Ok(Duration::from_nanos((self.nsecs - other.nsecs) as u64))
    }
}

impl ToString for SystemTime {
    fn to_string(&self) -> String {
        let secs = self.nsecs / 1_000_000_000;
        let nsecs = (self.nsecs % 1_000_000_000) as u32;

        let mut seconds_remaining = secs;

        // Calculate years
        let mut year = 1970;
        loop {
            let days_in_year = if is_leap_year(year) { 366 } else { 365 };
            let seconds_in_year = days_in_year * 24 * 60 * 60;

            if seconds_remaining < seconds_in_year {
                break;
            }

            seconds_remaining -= seconds_in_year;
            year += 1;
        }

        // Calculate month and day
        let days_in_month = [
            31,                                       // January
            if is_leap_year(year) { 29 } else { 28 }, // February
            31,                                       // March
            30,                                       // April
            31,                                       // May
            30,                                       // June
            31,                                       // July
            31,                                       // August
            30,                                       // September
            31,                                       // October
            30,                                       // November
            31,                                       // December
        ];

        let mut month = 0;
        let mut day_of_month = 0;

        let days_remaining = seconds_remaining / (24 * 60 * 60);
        seconds_remaining %= 24 * 60 * 60;

        let mut days_counted = 0;
        for (i, &days) in days_in_month.iter().enumerate() {
            if days_counted + days > days_remaining {
                month = i + 1; // 1-based month
                day_of_month = (days_remaining - days_counted) + 1; // 1-based day
                break;
            }
            days_counted += days;
        }

        // Calculate time components
        let hour = seconds_remaining / (60 * 60);
        seconds_remaining %= 60 * 60;
        let minute = seconds_remaining / 60;
        let second = seconds_remaining % 60;

        format!(
            "{:04}-{:02}-{:02} {:02}:{:02}:{:02}.{:09}",
            year, month, day_of_month, hour, minute, second, nsecs
        )
    }
}

fn is_leap_year(year: u128) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

impl Debug for SystemTime {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "SystemTime({} [ns] since epoch = {})",
            self.nsecs,
            self.to_string()
        )
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
/// Module for NTP and system clock.
///
/// This module provides the interface for NTP daemons and managing the system clock.
#[derive(Copy, Clone)]
pub struct SystemClock {}

impl SystemClock {
    pub fn new() -> Self {
        Self {}
    }

    pub fn now() -> SystemTime {
        ArchImpl::get_time()
    }

    pub fn set(new: u128) {
        ArchImpl::set_time(new);
    }
}

pub trait Ntp {
    /// Get the current time in nanoseconds.
    fn get_time() -> SystemTime;

    /// Set the current time in nanoseconds.
    fn set_time(new: u128);
    fn sync_time();
}
