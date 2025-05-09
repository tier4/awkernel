// TODO: Remove allow(dead_code).
#![allow(dead_code)]

use awkernel_lib::delay::wait_millisec;
use core::time::Duration;

#[cfg(feature = "seconds")]
pub(super) fn convert_duration(duration: u64) -> Duration {
    Duration::from_secs(duration)
}

#[cfg(feature = "milliseconds")]
pub(super) fn convert_duration(duration: u64) -> Duration {
    Duration::from_millis(duration)
}

#[cfg(feature = "microseconds")]
pub(super) fn convert_duration(duration: u64) -> Duration {
    Duration::from_micros(duration)
}

#[cfg(feature = "nanoseconds")]
pub(super) fn convert_duration(duration: u64) -> Duration {
    Duration::from_nanos(duration)
}

// default
#[cfg(not(any(
    feature = "seconds",
    feature = "milliseconds",
    feature = "microseconds",
    feature = "nanoseconds"
)))]
pub(super) fn convert_duration(duration: u64) -> Duration {
    Duration::from_millis(duration)
}

#[cfg(feature = "seconds")]
pub(super) fn simulated_execution_time(duration: u64) {
    wait_millisec(duration * 1000);
}

#[cfg(feature = "milliseconds")]
pub(super) fn simulated_execution_time(duration: u64) {
    wait_millisec(duration);
}

#[cfg(feature = "microseconds")]
pub(super) fn simulated_execution_time(duration: u64) {
    wait_millisec(duration / 1000);
}

#[cfg(feature = "nanoseconds")]
pub(super) fn simulated_execution_time(duration: u64) {
    wait_millisec(duration / 1000000);
}

// default
#[cfg(not(any(
    feature = "seconds",
    feature = "milliseconds",
    feature = "microseconds",
    feature = "nanoseconds"
)))]
pub(super) fn simulated_execution_time(duration: u64) -> u64 {
    duration
}
