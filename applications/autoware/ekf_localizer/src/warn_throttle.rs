// Copyright 2022 Autoware Foundation
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// Ported from the following versions of the original C++ code:
// core/autoware_core:
// type: git
// url: https://github.com/autowarefoundation/autoware_core.git
// original file path: localization/autoware_ekf_localizer/src/include/warning.hpp
// version: 1.8.0
//
// The actual throttle *algorithm* upstream's `Warning::warn_throttle` runs (via
// `RCLCPP_WARN_THROTTLE`) is not defined in autoware_ekf_localizer at all -- it lives in
// ROS 2 itself:
//   - rclcpp (humble): rclcpp/resource/logging.hpp.em, the `throttle` feature combination:
//       auto get_time_point = [&c=clock](rcutils_time_point_value_t * time_point) { ...
//         *time_point = c.now().nanoseconds(); ... };
//       RCUTILS_LOG_WARN_THROTTLE_NAMED(get_time_point, duration, ...);
//   - rcutils (humble): rcutils/resource/logging_macros.h.em,
//     `RCUTILS_LOG_CONDITION_THROTTLE_BEFORE(get_time_point_value, duration)`:
//       static rcutils_duration_value_t __rcutils_logging_duration = MS_TO_NS(duration);
//       static rcutils_time_point_value_t __rcutils_logging_last_logged = 0;
//       rcutils_time_point_value_t __rcutils_logging_now = 0;
//       get_time_point_value(&__rcutils_logging_now);
//       condition = __rcutils_logging_now >= __rcutils_logging_last_logged + __rcutils_logging_duration;
//       if (condition) { __rcutils_logging_last_logged = __rcutils_logging_now; ... log ... }
// `WarnThrottle` below is a direct port of that condition, using `now_ns` (this crate's u64
// timestamp convention) in place of `clock.now().nanoseconds()`. This crate has no ROS node,
// so the caller passes "now" explicitly instead of a node-owned `rclcpp::Clock`.
//
// RT NOTE: unlike upstream -- where e.g. `mahalanobis_warning_message(distance, ...)` is
// built (and its `std::string` allocated) as an eager argument to `warn_throttle`, so the
// formatting cost is paid on every call regardless of whether the throttle actually lets
// the message through -- `should_emit` is checked *before* the caller formats/logs
// anything, so the `log::warn!`/`log::error!` allocation (`alloc::format!` in awkernel's
// buffered logger) is itself skipped while throttled, not just the eventual UART write.
// This matters because these call sites live inside `EKFModule::measurement_update_pose`/
// `measurement_update_twist`, which are RT-critical (see `kalman_filter.rs`'s WCET
// contracts): under a sustained fault (a sensor failing the same gate every tick),
// unthrottled logging would otherwise allocate on every single tick.

#[derive(Debug, Clone)]
pub struct WarnThrottle {
    /// Matches upstream's `__rcutils_logging_last_logged`, which is a `static` initialized
    /// to `0`, not an "unset" sentinel -- see `should_emit` for why that matters on the
    /// very first call.
    last_logged_ns: u64,
    interval_ns: u64,
}

impl WarnThrottle {
    pub fn new(interval_ms: u64) -> Self {
        Self {
            last_logged_ns: 0,
            interval_ns: interval_ms * 1_000_000,
        }
    }

    /// Returns `true` (and records `now_ns` as the new last-logged time) exactly when
    /// upstream's `__rcutils_logging_now >= __rcutils_logging_last_logged + __rcutils_logging_duration`
    /// would be true. Two consequences of matching this literally, both confirmed against
    /// the rcutils source above rather than assumed:
    /// - Since `last_logged_ns` starts at `0` (not "never logged"), the very first call
    ///   only emits if `now_ns >= interval_ns`. With a small/near-zero `now_ns` (e.g. replaying
    ///   a recorded run whose timestamps start near zero, as this project's own evaluation
    ///   data does), the first would-be warning is suppressed, exactly like upstream -- it is
    ///   *not* unconditionally emitted the way a "first call always logs" design would.
    /// - A backwards time jump (`now_ns` older than `last_logged_ns`) makes the sum
    ///   `last_logged_ns + interval_ns` exceed `now_ns`, so the condition is false: upstream
    ///   *suppresses* on a clock jump back, it does not fail open.
    ///
    /// WCET contract: no heap allocation, no panic (uses `saturating_add` to rule out
    /// overflow even though realistic timestamps never approach `u64::MAX`), O(1), no
    /// logging/formatting/I/O of its own -- this only decides whether the *caller* should
    /// log.
    pub fn should_emit(&mut self, now_ns: u64) -> bool {
        let condition = now_ns >= self.last_logged_ns.saturating_add(self.interval_ns);
        if condition {
            self.last_logged_ns = now_ns;
        }
        condition
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // None of the tests below port an upstream `test_*.cpp` file -- as noted in this
    // file's header, the throttle algorithm belongs to ROS 2's `rcutils`, not
    // `autoware_ekf_localizer`, and `rcutils`'s own unit tests are out of scope for this
    // repository. These tests instead verify this crate's `WarnThrottle` against the
    // `RCUTILS_LOG_CONDITION_THROTTLE_BEFORE` macro semantics quoted above.

    #[test]
    fn suppresses_the_first_call_when_now_is_below_the_interval() {
        // last_logged_ns starts at 0, so now=0 with a 2s interval must NOT emit --
        // matching rcutils' `0 >= 0 + duration` being false for any positive duration.
        let mut t = WarnThrottle::new(2000);
        assert!(!t.should_emit(0));
        assert!(!t.should_emit(1_999_999_999));
    }

    #[test]
    fn emits_the_first_call_once_now_reaches_the_interval() {
        let mut t = WarnThrottle::new(2000);
        assert!(t.should_emit(2_000_000_000));
    }

    #[test]
    fn suppresses_within_the_interval_after_an_emit() {
        let mut t = WarnThrottle::new(2000);
        assert!(t.should_emit(2_000_000_000));
        assert!(!t.should_emit(3_000_000_000)); // 1s later, interval is 2s
        assert!(!t.should_emit(3_999_999_999));
    }

    #[test]
    fn emits_again_once_the_interval_elapses() {
        let mut t = WarnThrottle::new(2000);
        assert!(t.should_emit(2_000_000_000));
        assert!(t.should_emit(4_000_000_000)); // exactly 2s after the last emit
    }

    #[test]
    fn suppresses_on_a_backwards_time_jump() {
        // Matches rcutils exactly: now < last_logged makes `now >= last_logged + duration`
        // false, so a clock jump back suppresses rather than fail-opening.
        let mut t = WarnThrottle::new(2000);
        assert!(t.should_emit(5_000_000_000));
        assert!(!t.should_emit(1_000_000_000));
    }
}
