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

/// Perform `duration` of work-bound computation (see `awkernel_lib::busy_work`):
/// time spent preempted does not count toward it, unlike a wall-clock wait.
#[cfg(any(
    feature = "seconds",
    feature = "milliseconds",
    feature = "microseconds",
    feature = "nanoseconds"
))]
pub(super) fn simulated_execution_time(duration: u64) {
    awkernel_lib::busy_work::spin_work(convert_duration(duration));
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
