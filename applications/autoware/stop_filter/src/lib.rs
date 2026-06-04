//! Stop filter: zeroes all twist components when the vehicle is below
//! velocity thresholds, indicating a stationary state.
//!
//! Ported from TECS t_stop_filter_impl.rs / autoware_stop_filter stop_filter.cpp.
#![no_std]

use localization_types::KinematicState;

pub const DEFAULT_VX_THRESHOLD: f64 = 0.0;
pub const DEFAULT_WZ_THRESHOLD: f64 = 0.0;

/// Returns `true` when both longitudinal velocity and yaw rate are below
/// their respective thresholds (strict less-than, matching C++ original).
#[inline]
pub fn is_stopped(ks: &KinematicState, vx_threshold: f64, wz_threshold: f64) -> bool {
    ks.twist.twist.linear.x.abs() < vx_threshold
        && ks.twist.twist.angular.z.abs() < wz_threshold
}

/// Apply the stop filter.
///
/// Clones the full `KinematicState` and, when stopped, overwrites the six
/// twist velocity components with zero.  Pose, accel, and all covariance
/// matrices are preserved unchanged — matching the Autoware Core behaviour of
/// `create_filtered_msg()` in stop_filter_node.cpp.
pub fn apply(ks: KinematicState, vx_threshold: f64, wz_threshold: f64) -> KinematicState {
    if is_stopped(&ks, vx_threshold, wz_threshold) {
        let mut out = ks;
        out.twist.twist.linear.x = 0.0;
        out.twist.twist.linear.y = 0.0;
        out.twist.twist.linear.z = 0.0;
        out.twist.twist.angular.x = 0.0;
        out.twist.twist.angular.y = 0.0;
        out.twist.twist.angular.z = 0.0;
        out
    } else {
        ks
    }
}
