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
pub(super) fn simulated_execution_time_normal(duration: u64) {
    wait_millisec(duration);
}

#[cfg(feature = "milliseconds")]
pub(super) fn simulated_execution_time(duration: u64) {
    let rand_time = awkernel_lib::time::Time::now().uptime().as_nanos() as u64;
    let random_offset = rand_time % 50;
    let wait_duration = duration + random_offset;
    wait_millisec(wait_duration);
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
