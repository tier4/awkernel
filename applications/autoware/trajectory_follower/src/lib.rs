//! Simple trajectory follower using linearised pure-pursuit lateral control
//! and a P-controller for longitudinal speed.
//!
//! Ported from TECS t_simple_trajectory_follower_impl.rs,
//! t_utils_trajectory_array_impl.rs, t_utils_pose_deviation_impl.rs.
#![no_std]

use awkernel_lib::sync::{mcs::MCSNode, mutex::Mutex};
use localization_types::{AccelWithCovarianceStamped, Control, KinematicState, TrajectoryPoint};

// ---------------------------------------------------------------------------
// Compile-time constants (constexpr in C++ — not ROS parameters)
// ---------------------------------------------------------------------------

const WHEEL_BASE: f64 = 4.0;
const LOOKAHEAD_TIME: f64 = 3.0;
const MIN_LOOKAHEAD: f64 = 3.0;
const STEER_LIM: f64 = 0.6;
const KP_LONGITUDINAL: f64 = 0.5;
const ACC_LIM: f64 = 2.0;

// ---------------------------------------------------------------------------
// Runtime configuration (ROS parameters in C++)
// ---------------------------------------------------------------------------

struct TrajFollowerConfig {
    use_external_target_vel: bool,
    external_target_vel: f64,
    lateral_deviation: f64,
}

impl TrajFollowerConfig {
    const fn new() -> Self {
        Self {
            use_external_target_vel: true,
            external_target_vel: 5.0,
            lateral_deviation: 0.0,
        }
    }
}

static CONFIG: Mutex<TrajFollowerConfig> = Mutex::new(TrajFollowerConfig::new());

/// Set ROS parameters.  Mirrors `use_external_target_vel`, `external_target_vel`,
/// and `lateral_deviation` in simple_trajectory_follower.launch.xml.
/// Call once at node initialisation.
pub fn configure(use_external_target_vel: bool, external_target_vel: f64, lateral_deviation: f64) {
    let mut node = MCSNode::new();
    let mut cfg = CONFIG.lock(&mut node);
    cfg.use_external_target_vel = use_external_target_vel;
    cfg.external_target_vel = external_target_vel;
    cfg.lateral_deviation = lateral_deviation;
}

// ---------------------------------------------------------------------------
// Fixed waypoints: straight line along the X-axis from 0 m to 18 m.
// ---------------------------------------------------------------------------

const FIX_POINTS: [TrajectoryPoint; 10] = [
    TrajectoryPoint::new(0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0),
    TrajectoryPoint::new(2.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0),
    TrajectoryPoint::new(4.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 2.0),
    TrajectoryPoint::new(6.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 3.0),
    TrajectoryPoint::new(8.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 4.0),
    TrajectoryPoint::new(10.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 5.0),
    TrajectoryPoint::new(12.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 5.0),
    TrajectoryPoint::new(14.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 5.0),
    TrajectoryPoint::new(16.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 2.5),
    TrajectoryPoint::new(18.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0),
];

// ---------------------------------------------------------------------------
// Geometry helpers (ported from t_utils_pose_deviation_impl.rs)
// ---------------------------------------------------------------------------

/// Extract yaw angle from a unit quaternion (z-up, planar rotation).
/// Quaternion convention in nalgebra: `Quaternion::new(w, i, j, k)`.
fn extract_yaw(q: &nalgebra::Quaternion<f64>) -> f64 {
    let siny_cosp = 2.0 * (q.w * q.k + q.i * q.j);
    let cosy_cosp = 1.0 - 2.0 * (q.j * q.j + q.k * q.k);
    libm::atan2(siny_cosp, cosy_cosp)
}

/// Signed lateral deviation of `target_point` from `base_pose` (cross-product
/// method, equivalent to `autoware_utils_geometry::calc_lateral_deviation`).
fn calc_lateral_deviation(
    base_pose: &localization_types::Pose,
    target_point: &nalgebra::Vector3<f64>,
) -> f64 {
    let yaw = extract_yaw(&base_pose.orientation);
    let base_unit = nalgebra::Vector3::new(libm::cos(yaw), libm::sin(yaw), 0.0);
    let diff = nalgebra::Vector3::new(
        target_point.x - base_pose.point.x,
        target_point.y - base_pose.point.y,
        0.0,
    );
    base_unit.cross(&diff).z
}

/// Signed yaw deviation from `base_pose` to `target_pose`, normalised to
/// [-π, π) (equivalent to `autoware_utils_geometry::calc_yaw_deviation`).
fn calc_yaw_deviation(
    base_pose: &localization_types::Pose,
    target_pose: &localization_types::Pose,
) -> f64 {
    let base_yaw = extract_yaw(&base_pose.orientation);
    let target_yaw = extract_yaw(&target_pose.orientation);
    let mut d = target_yaw - base_yaw;
    while d >= core::f64::consts::PI {
        d -= 2.0 * core::f64::consts::PI;
    }
    while d < -core::f64::consts::PI {
        d += 2.0 * core::f64::consts::PI;
    }
    d
}

// ---------------------------------------------------------------------------
// Trajectory utilities (ported from t_utils_trajectory_array_impl.rs)
// ---------------------------------------------------------------------------

/// Return the index of the trajectory point closest to `query` in the XY
/// plane (Euclidean distance, ignoring Z).
fn find_nearest_index(points: &[TrajectoryPoint], query: &nalgebra::Vector3<f64>) -> usize {
    let mut best_idx = 0usize;
    let mut best_dist2 = f64::MAX;
    for (i, p) in points.iter().enumerate() {
        let dx = p.pose.point.x - query.x;
        let dy = p.pose.point.y - query.y;
        let d2 = dx * dx + dy * dy;
        if d2 < best_dist2 {
            best_dist2 = d2;
            best_idx = i;
        }
    }
    best_idx
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Compute a `Control` command from the current kinematic state.
///
/// `accel` is wired in for API completeness (mirrors TECS signature) but is
/// not used in the current pure-pursuit + P-controller implementation.
pub fn follow(ks: &KinematicState, _accel: &AccelWithCovarianceStamped) -> Control {
    // Read all runtime parameters in one lock.
    let (use_external_target_vel, external_target_vel, lateral_deviation) = {
        let mut node = MCSNode::new();
        let cfg = CONFIG.lock(&mut node);
        (cfg.use_external_target_vel, cfg.external_target_vel, cfg.lateral_deviation)
    };

    let ego_pos = &ks.pose.pose.point;

    // 1. Find the closest trajectory point.
    let closest_idx = find_nearest_index(&FIX_POINTS, ego_pos).min(FIX_POINTS.len() - 1);
    let closest = &FIX_POINTS[closest_idx];

    // Timestamp is captured here — after updateClosest, before calcSteerCmd/calcAccCmd.
    // Mirrors the order in simple_trajectory_follower.cpp onTimer().
    let now = awkernel_lib::time::Time::now();

    // 2. Lateral control: linearised pure pursuit.
    let lat_err = calc_lateral_deviation(&closest.pose, ego_pos) - lateral_deviation;
    let yaw_err = calc_yaw_deviation(&closest.pose, &ks.pose.pose);

    let vx = ks.twist.twist.linear.x;
    let lookahead = MIN_LOOKAHEAD + LOOKAHEAD_TIME * vx.abs();
    let kp_lat = 2.0 * WHEEL_BASE / (lookahead * lookahead);
    let kd_yaw = 2.0 * WHEEL_BASE / lookahead;
    let steer = (-kp_lat * lat_err - kd_yaw * yaw_err)
        .max(-STEER_LIM)
        .min(STEER_LIM);

    // 3. Longitudinal control: P-controller on velocity error.
    let traj_vel = closest.longitudinal_velocity_mps;
    let target_vel = if use_external_target_vel { external_target_vel } else { traj_vel };
    let vel_err = vx - target_vel;
    let acc = (-KP_LONGITUDINAL * vel_err).max(-ACC_LIM).min(ACC_LIM);

    // 4. Fill output.
    let mut ctrl = Control::default();
    ctrl.stamp = now;
    ctrl.lateral.stamp = now;
    ctrl.lateral.steering_tire_angle = steer;
    ctrl.longitudinal.stamp = now;
    ctrl.longitudinal.velocity = target_vel;
    ctrl.longitudinal.acceleration = acc;

    ctrl
}
