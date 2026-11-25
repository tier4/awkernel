// Copyright 2018-2019 Autoware Foundation
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
// original file path: localization/autoware_ekf_localizer/src/ekf_module.cpp
// version: 1.8.0
//
// NOTE: upstream has no `test_ekf_module.cpp` at this tag (confirmed against the actual
// `localization/autoware_ekf_localizer/test/` tree) -- `EKFModule` itself is not unit
// tested upstream. The `#[cfg(test)] mod tests` below is therefore this crate's own
// integration-level test suite for `EKFModule`, not a port of an upstream test file.
//
// See src/kalman_filter.rs, src/state_transition.rs, src/measurement.rs,
// src/mahalanobis.rs, src/covariance.rs and src/numeric.rs for the upstream files each
// module corresponds to (each of those does have an upstream test file, ported alongside).

#![no_std]
#![allow(non_snake_case)]

extern crate alloc;

mod covariance;
mod kalman_filter;
mod mahalanobis;
mod measurement;
mod numeric;
mod state_transition;
mod warn_throttle;

use alloc::{vec, vec::Vec};
pub use common_types::Header;
use core::ptr::null_mut;
use core::sync::atomic::{AtomicPtr, Ordering as AtomicOrdering};
use libm::{atan2, cos, sin};
use nalgebra::{
    DMatrix, DVector, Matrix6, Quaternion as NQuaternion, Unit, UnitQuaternion, Vector3, Vector6,
};

pub use imu_corrector::Transform;
pub use vehicle_velocity_converter::{TwistWithCovariance, TwistWithCovarianceStamped};

use covariance::{
    ekf_covariance_to_pose_message_covariance, ekf_covariance_to_twist_message_covariance,
};
use kalman_filter::DelayCompensatedKalmanFilter;
use mahalanobis::mahalanobis;
use measurement::{
    pose_measurement_covariance, pose_measurement_matrix, twist_measurement_covariance,
    twist_measurement_matrix,
};
use numeric::{has_inf, has_nan};
use state_transition::{
    create_state_transition_matrix, normalize_yaw, predict_next_state, process_noise_covariance,
};
use warn_throttle::WarnThrottle;

static EKF_MODULE_INSTANCE: AtomicPtr<EKFModule> = AtomicPtr::new(null_mut());

// XYZRPY (6x6, row-major) covariance array indices, same layout as measurement.rs/covariance.rs.
const POSE_COV_X_X: usize = 0;
const POSE_COV_Y_Y: usize = 7;
const POSE_COV_Z_Z: usize = 14;
const POSE_COV_ROLL_ROLL: usize = 21;
const POSE_COV_PITCH_PITCH: usize = 28;
const POSE_COV_YAW_YAW: usize = 35;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StateIndex {
    X = 0,
    Y = 1,
    Yaw = 2,
    YawBias = 3,
    Vx = 4,
    Wz = 5,
}

pub type StateVector = Vector6<f64>;
pub type StateCovariance = Matrix6<f64>;

#[derive(Debug, Clone, Copy)]
pub struct Point3D {
    pub x: f64,
    pub y: f64,
    pub z: f64,
}

#[derive(Debug, Clone, Copy)]
pub struct Quaternion {
    pub x: f64,
    pub y: f64,
    pub z: f64,
    pub w: f64,
}

#[derive(Debug, Clone, Copy)]
pub struct Pose {
    pub position: Point3D,
    pub orientation: Quaternion,
}

/// Equivalent to ROS `geometry_msgs/PoseStamped` (`ros2/common_interfaces`, the message
/// definitions repo -- not `ros2/geometry2`, which only consumes these types):
/// `EKFModule::get_current_pose`'s output, as opposed to `Pose` which is the
/// (header-less) value itself.
#[derive(Debug, Clone)]
pub struct PoseStamped {
    pub header: common_types::Header,
    pub pose: Pose,
}

#[derive(Debug, Clone, Copy)]
pub struct Twist {
    pub linear: Vector3<f64>,
    pub angular: Vector3<f64>,
}

/// Equivalent to ROS `geometry_msgs/TwistStamped` (`ros2/common_interfaces`):
/// `EKFModule::get_current_twist`'s output.
#[derive(Debug, Clone)]
pub struct TwistStamped {
    pub header: common_types::Header,
    pub twist: Twist,
}

#[derive(Debug, Clone, Copy)]
pub struct PoseWithCovariance {
    pub pose: Pose,
    pub covariance: [f64; 36],
}

/// Equivalent to ROS `geometry_msgs/PoseWithCovarianceStamped` (`ros2/common_interfaces`):
/// a timestamped pose measurement, as opposed to `PoseWithCovariance` which is the
/// (header-less) payload embedded in `EKFOdometry` output.
#[derive(Debug, Clone)]
pub struct PoseWithCovarianceStamped {
    pub header: common_types::Header,
    pub pose: PoseWithCovariance,
}

/// Equivalent to ROS `nav_msgs/Odometry` (`ros2/common_interfaces`): the aggregated
/// output message combining pose, twist, and frame metadata, as opposed to `EKFModule`'s
/// individual getters
/// (`get_current_pose_with_covariance`, `get_current_twist_covariance`, etc.) which this
/// type is meant to be assembled from at the pub/sub layer.
#[derive(Debug, Clone)]
pub struct EKFOdometry {
    pub header: common_types::Header,
    pub child_frame_id: &'static str,
    pub pose: PoseWithCovariance,
    pub twist: TwistWithCovariance,
}

#[derive(Debug, Clone)]
pub struct EKFParameters {
    pub enable_yaw_bias_estimation: bool,
    pub extend_state_step: usize,
    pub proc_stddev_vx_c: f64,
    pub proc_stddev_wz_c: f64,
    pub proc_stddev_yaw_c: f64,
    pub z_filter_proc_dev: f64,
    pub roll_filter_proc_dev: f64,
    pub pitch_filter_proc_dev: f64,
    pub pose_frame_id: &'static str,
    pub pose_additional_delay: f64,
    pub pose_gate_dist: f64,
    pub pose_smoothing_steps: usize,
    pub twist_additional_delay: f64,
    pub twist_gate_dist: f64,
    pub twist_smoothing_steps: usize,
    /// Below this |vx| [m/s], the vx observation is considered unreliable (wheel-speed
    /// sensor quantization/slip near zero speed) and its variance should be inflated by
    /// the caller via `apply_twist_observability_gate` before calling
    /// `measurement_update_twist`. `0.0` disables the gate (upstream's own default).
    pub threshold_observable_velocity_mps: f64,
}

impl Default for EKFParameters {
    fn default() -> Self {
        Self {
            enable_yaw_bias_estimation: true,
            extend_state_step: 50,
            proc_stddev_vx_c: 10.0,
            proc_stddev_wz_c: 5.0,
            proc_stddev_yaw_c: 0.005,
            z_filter_proc_dev: 5.0,
            roll_filter_proc_dev: 0.1,
            pitch_filter_proc_dev: 0.1,
            pose_frame_id: "map",
            pose_additional_delay: 0.0,
            pose_gate_dist: 49.5,
            pose_smoothing_steps: 5,
            twist_additional_delay: 0.0,
            twist_gate_dist: 46.1,
            twist_smoothing_steps: 2,
            threshold_observable_velocity_mps: 0.0,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Simple1DFilter {
    initialized: bool,
    x: f64,
    var: f64,
    proc_var_x_c: f64,
}

impl Simple1DFilter {
    pub fn new() -> Self {
        Self {
            initialized: false,
            x: 0.0,
            var: 1e9,
            proc_var_x_c: 0.0,
        }
    }

    pub fn init(&mut self, init_obs: f64, obs_var: f64) {
        self.x = init_obs;
        self.var = obs_var;
        self.initialized = true;
    }

    pub fn update(&mut self, obs: f64, obs_var: f64, dt: f64) {
        if !self.initialized {
            self.init(obs, obs_var);
            return;
        }

        let proc_var_x_d = self.proc_var_x_c * dt * dt;
        self.var += proc_var_x_d;

        let kalman_gain = self.var / (self.var + obs_var);
        self.x += kalman_gain * (obs - self.x);
        self.var = (1.0 - kalman_gain) * self.var;
    }

    pub fn set_proc_var(&mut self, proc_var: f64) {
        self.proc_var_x_c = proc_var;
    }

    pub fn get_x(&self) -> f64 {
        self.x
    }

    pub fn get_var(&self) -> f64 {
        self.var
    }
}

impl Default for Simple1DFilter {
    fn default() -> Self {
        Self::new()
    }
}

fn to_dvector(v: &StateVector) -> DVector<f64> {
    let mut out = DVector::zeros(6);
    for i in 0..6 {
        out[i] = v[i];
    }
    out
}

fn to_state_vector(v: &DVector<f64>) -> StateVector {
    let mut out = StateVector::zeros();
    for i in 0..6 {
        out[i] = v[i];
    }
    out
}

fn to_dmatrix(m: &StateCovariance) -> DMatrix<f64> {
    let mut out = DMatrix::zeros(6, 6);
    for i in 0..6 {
        for j in 0..6 {
            out[(i, j)] = m[(i, j)];
        }
    }
    out
}

#[derive(Debug, Clone)]
pub struct EKFModule {
    params: EKFParameters,
    kf: DelayCompensatedKalmanFilter,
    z_filter: Simple1DFilter,
    roll_filter: Simple1DFilter,
    pitch_filter: Simple1DFilter,
    accumulated_delay_times: Vec<f64>,
    /// Angular velocity from the most recent successful twist update, used by
    /// `compensate_rph_with_delay` to extrapolate roll/pitch/z across the pose's delay.
    last_angular_velocity: Vector3<f64>,
    ekf_dt: f64,
    // RT NOTE: the measurement matrices C are constant (only the state layout picks which
    // components are observed), so they are built once here instead of every
    // measurement_update_pose/twist call.
    pose_measurement_matrix: DMatrix<f64>,
    twist_measurement_matrix: DMatrix<f64>,
    // Mirrors upstream's per-call-site `RCLCPP_WARN_THROTTLE` durations (see
    // `warning_message.cpp`): one independent throttle per warning site so a stuck sensor
    // failing one gate every tick doesn't also suppress warnings from a different gate.
    pose_frame_id_warn: WarnThrottle,
    pose_delay_time_warn: WarnThrottle,
    pose_delay_step_warn: WarnThrottle,
    pose_mahalanobis_warn: WarnThrottle,
    twist_frame_id_warn: WarnThrottle,
    twist_delay_time_warn: WarnThrottle,
    twist_delay_step_warn: WarnThrottle,
    twist_mahalanobis_warn: WarnThrottle,
}

impl EKFModule {
    pub fn new(params: EKFParameters) -> Self {
        let x0 = StateVector::zeros();
        let mut p0 = StateCovariance::identity() * 1e15;

        p0[(StateIndex::Yaw as usize, StateIndex::Yaw as usize)] = 50.0;
        if params.enable_yaw_bias_estimation {
            p0[(StateIndex::YawBias as usize, StateIndex::YawBias as usize)] = 50.0;
        }
        p0[(StateIndex::Vx as usize, StateIndex::Vx as usize)] = 1000.0;
        p0[(StateIndex::Wz as usize, StateIndex::Wz as usize)] = 50.0;

        let mut kf = DelayCompensatedKalmanFilter::new();
        kf.init(&to_dvector(&x0), &to_dmatrix(&p0), params.extend_state_step);

        let mut z_filter = Simple1DFilter::new();
        let mut roll_filter = Simple1DFilter::new();
        let mut pitch_filter = Simple1DFilter::new();

        z_filter.set_proc_var(params.z_filter_proc_dev * params.z_filter_proc_dev);
        roll_filter.set_proc_var(params.roll_filter_proc_dev * params.roll_filter_proc_dev);
        pitch_filter.set_proc_var(params.pitch_filter_proc_dev * params.pitch_filter_proc_dev);

        let accumulated_delay_times = vec![1e15; params.extend_state_step];

        Self {
            params,
            kf,
            z_filter,
            roll_filter,
            pitch_filter,
            accumulated_delay_times,
            last_angular_velocity: Vector3::zeros(),
            ekf_dt: 0.0,
            pose_measurement_matrix: pose_measurement_matrix(),
            twist_measurement_matrix: twist_measurement_matrix(),
            // Durations match upstream's literal `warn_throttle(..., N)` call sites.
            pose_frame_id_warn: WarnThrottle::new(2000),
            pose_delay_time_warn: WarnThrottle::new(1000),
            pose_delay_step_warn: WarnThrottle::new(2000),
            pose_mahalanobis_warn: WarnThrottle::new(2000),
            twist_frame_id_warn: WarnThrottle::new(2000),
            twist_delay_time_warn: WarnThrottle::new(1000),
            twist_delay_step_warn: WarnThrottle::new(2000),
            twist_mahalanobis_warn: WarnThrottle::new(2000),
        }
    }

    /// TF-aware initialization: `transform` is the already-resolved
    /// `initial_pose.header.frame_id -> base_link` (or map -> odom, depending on wiring)
    /// transform, applied the same way upstream's `initialize()` does by adding it to the
    /// pose before seeding the filter. Looking up the transform itself is out of scope here
    /// (see `imu_corrector::TransformListener` for that half of the existing port pattern).
    pub fn initialize(&mut self, initial_pose: &PoseWithCovarianceStamped, transform: &Transform) {
        let mut x0 = StateVector::zeros();
        x0[StateIndex::X as usize] = initial_pose.pose.pose.position.x + transform.translation.x;
        x0[StateIndex::Y as usize] = initial_pose.pose.pose.position.y + transform.translation.y;

        let transform_yaw = self.quaternion_to_yaw(Quaternion {
            x: transform.rotation.x,
            y: transform.rotation.y,
            z: transform.rotation.z,
            w: transform.rotation.w,
        });
        x0[StateIndex::Yaw as usize] =
            self.quaternion_to_yaw(initial_pose.pose.pose.orientation) + transform_yaw;
        x0[StateIndex::YawBias as usize] = 0.0;
        x0[StateIndex::Vx as usize] = 0.0;
        x0[StateIndex::Wz as usize] = 0.0;

        let mut p0 = StateCovariance::zeros();
        p0[(StateIndex::X as usize, StateIndex::X as usize)] =
            initial_pose.pose.covariance[POSE_COV_X_X];
        p0[(StateIndex::Y as usize, StateIndex::Y as usize)] =
            initial_pose.pose.covariance[POSE_COV_Y_Y];
        p0[(StateIndex::Yaw as usize, StateIndex::Yaw as usize)] =
            initial_pose.pose.covariance[POSE_COV_YAW_YAW];
        if self.params.enable_yaw_bias_estimation {
            p0[(StateIndex::YawBias as usize, StateIndex::YawBias as usize)] = 0.0001;
        }
        p0[(StateIndex::Vx as usize, StateIndex::Vx as usize)] = 0.01;
        p0[(StateIndex::Wz as usize, StateIndex::Wz as usize)] = 0.01;

        self.kf.init(
            &to_dvector(&x0),
            &to_dmatrix(&p0),
            self.params.extend_state_step,
        );

        let z = initial_pose.pose.pose.position.z;
        let (roll, pitch, _yaw) = self.quaternion_to_rpy(initial_pose.pose.pose.orientation);

        let z_var = initial_pose.pose.covariance[POSE_COV_Z_Z];
        let roll_var = initial_pose.pose.covariance[POSE_COV_ROLL_ROLL];
        let pitch_var = initial_pose.pose.covariance[POSE_COV_PITCH_PITCH];

        self.z_filter.init(z, z_var);
        self.roll_filter.init(roll, roll_var);
        self.pitch_filter.init(pitch, pitch_var);
    }

    /// Matches upstream `EKFModule::predict_with_delay` exactly: it does *not* touch the
    /// delay-time buffer. Upstream's node (`EKFLocalizer::timer_callback`) calls
    /// `accumulate_delay_time(dt)` and `predict_with_delay(dt)` as two separate sibling
    /// calls (see `update_predict_frequency` vs. the prediction block in `timer_callback`);
    /// callers of this crate must do the same, with the same `dt`, once per predict tick.
    pub fn predict_with_delay(&mut self, dt: f64) {
        let x_curr = to_state_vector(&self.kf.latest_x());

        let vx_term = self.params.proc_stddev_vx_c * dt;
        let wz_term = self.params.proc_stddev_wz_c * dt;
        let yaw_term = self.params.proc_stddev_yaw_c * dt;

        let x_next = predict_next_state(&x_curr, dt);
        let a = create_state_transition_matrix(&x_curr, dt);
        let q = process_noise_covariance(yaw_term * yaw_term, vx_term * vx_term, wz_term * wz_term);

        self.kf
            .predict_with_delay(&to_dvector(&x_next), &to_dmatrix(&a), &to_dmatrix(&q));

        self.ekf_dt = dt;
    }

    pub fn get_current_pose(&self, get_biased_yaw: bool, current_time: u64) -> PoseStamped {
        let z = self.z_filter.get_x();
        let roll = self.roll_filter.get_x();
        let pitch = self.pitch_filter.get_x();

        let x_vec = self.kf.latest_x();
        let x = x_vec[StateIndex::X as usize];
        let y = x_vec[StateIndex::Y as usize];
        let biased_yaw = x_vec[StateIndex::Yaw as usize];
        let yaw_bias = x_vec[StateIndex::YawBias as usize];

        let yaw = if get_biased_yaw {
            biased_yaw
        } else {
            biased_yaw + yaw_bias
        };

        PoseStamped {
            header: common_types::Header {
                frame_id: self.params.pose_frame_id,
                timestamp: current_time,
            },
            pose: Pose {
                position: Point3D { x, y, z },
                orientation: self.rpy_to_quaternion(roll, pitch, yaw),
            },
        }
    }

    pub fn get_current_twist(&self, current_time: u64) -> TwistStamped {
        let x_vec = self.kf.latest_x();
        let vx = x_vec[StateIndex::Vx as usize];
        let wz = x_vec[StateIndex::Wz as usize];

        TwistStamped {
            header: common_types::Header {
                frame_id: "base_link",
                timestamp: current_time,
            },
            twist: Twist {
                linear: Vector3::new(vx, 0.0, 0.0),
                angular: Vector3::new(0.0, 0.0, wz),
            },
        }
    }

    pub fn get_yaw_bias(&self) -> f64 {
        self.kf.latest_x()[StateIndex::YawBias as usize]
    }

    // Not a port of any upstream `EKFModule` method (see `ekf_module.hpp`'s public API); a
    // convenience wrapper bundling `get_current_pose`/`get_current_pose_covariance` for
    // `EKFOdometry` assembly.
    pub fn get_current_pose_with_covariance(&self, current_time: u64) -> PoseWithCovariance {
        let pose = self.get_current_pose(false, current_time).pose;
        let pose_covariance = self.get_current_pose_covariance();
        PoseWithCovariance {
            pose,
            covariance: pose_covariance,
        }
    }

    pub fn get_current_pose_covariance(&self) -> [f64; 36] {
        let mut cov = ekf_covariance_to_pose_message_covariance(&self.kf.latest_p());
        cov[POSE_COV_Z_Z] = self.z_filter.get_var();
        cov[POSE_COV_ROLL_ROLL] = self.roll_filter.get_var();
        cov[POSE_COV_PITCH_PITCH] = self.pitch_filter.get_var();
        cov
    }

    pub fn get_current_twist_covariance(&self) -> [f64; 36] {
        ekf_covariance_to_twist_message_covariance(&self.kf.latest_p())
    }

    /// Fuses an external pose measurement (e.g. NDT/GNSS localization) at delay step
    /// `find_closest_delay_time_index(t_curr - pose.header.timestamp)`. Returns `false`
    /// (state left untouched) if the delay exceeds `extend_state_step`, the measurement
    /// fails the Mahalanobis gate, or it contains NaN/Inf.
    ///
    /// There is deliberately no "MRM mode" gate here (or on `measurement_update_twist`).
    /// Switching into dead-reckoning is done entirely by whether `pose_with_covariance` is
    /// being published at all -- upstream's node only calls this when its pose queue is
    /// non-empty, so during MRM the queue is simply always empty and this is never
    /// invoked. `measurement_update_twist` keeps running throughout (Dead Reckoning
    /// explicitly still uses twist). That decision belongs entirely to the pub/sub wiring
    /// layer, not to `EKFModule`.
    pub fn measurement_update_pose(
        &mut self,
        pose: &PoseWithCovarianceStamped,
        t_curr: u64,
    ) -> bool {
        if pose.header.frame_id != self.params.pose_frame_id
            && self.pose_frame_id_warn.should_emit(t_curr)
        {
            log::warn!(
                "pose frame_id is {}, but pose_frame is set as {}. They must be same.",
                pose.header.frame_id,
                self.params.pose_frame_id
            );
        }

        let mut delay_time = nanos_to_seconds_delta(t_curr, pose.header.timestamp)
            + self.params.pose_additional_delay;
        if delay_time < 0.0 && self.pose_delay_time_warn.should_emit(t_curr) {
            log::warn!("[EKF] pose delay time is negative: {delay_time}. Treated as 0.");
        }
        delay_time = delay_time.max(0.0);

        let delay_step = self.find_closest_delay_time_index(delay_time);
        if delay_step >= self.params.extend_state_step {
            if self.pose_delay_step_warn.should_emit(t_curr) {
                log::warn!(
                    "[EKF] pose delay step {delay_step} exceeds extend_state_step {}. Ignoring measurement.",
                    self.params.extend_state_step
                );
            }
            return false;
        }

        let ekf_yaw = self.kf.x_element(delay_step, StateIndex::Yaw as usize);
        let raw_yaw = self.quaternion_to_yaw(pose.pose.pose.orientation);
        let yaw_error = normalize_yaw(raw_yaw - ekf_yaw);
        let yaw = yaw_error + ekf_yaw;

        let y = DVector::from_vec(vec![
            pose.pose.pose.position.x,
            pose.pose.pose.position.y,
            yaw,
        ]);
        if has_nan(&y) || has_inf(&y) {
            log::warn!("[EKF] pose measurement includes NaN or Inf. ignore update.");
            return false;
        }

        let y_ekf = DVector::from_vec(vec![
            self.kf.x_element(delay_step, StateIndex::X as usize),
            self.kf.x_element(delay_step, StateIndex::Y as usize),
            ekf_yaw,
        ]);
        let p_curr = self.kf.latest_p();
        let p_y = p_curr.view((0, 0), (3, 3)).clone_owned();

        let distance = mahalanobis(&y_ekf, &y, &p_y);
        if distance > self.params.pose_gate_dist {
            if self.pose_mahalanobis_warn.should_emit(t_curr) {
                log::warn!(
                    "[EKF] pose Mahalanobis distance {distance} exceeds gate {}. Ignore the measurement data.",
                    self.params.pose_gate_dist
                );
            }
            return false;
        }

        let r =
            pose_measurement_covariance(&pose.pose.covariance, self.params.pose_smoothing_steps);

        if !self
            .kf
            .update_with_delay(&y, &self.pose_measurement_matrix, &r, delay_step)
        {
            return false;
        }

        let pose_with_delay = self.compensate_rph_with_delay(pose, delay_time);
        self.update_simple_1d_filters(&pose_with_delay, self.params.pose_smoothing_steps);

        true
    }

    /// Extrapolates `pose`'s orientation/z forward by `delay_time` using
    /// `last_angular_velocity` (from the most recent twist update), so that the
    /// Simple1DFilters for z/roll/pitch are updated against a value consistent with
    /// "now" rather than the pose's original (delayed) timestamp.
    fn compensate_rph_with_delay(
        &self,
        pose: &PoseWithCovarianceStamped,
        delay_time: f64,
    ) -> PoseWithCovarianceStamped {
        let av = self.last_angular_velocity;
        let av_len = av.norm();

        let delta_orientation = if av_len > 0.0 {
            let axis = Unit::new_normalize(av);
            UnitQuaternion::from_axis_angle(&axis, av_len * delay_time)
        } else {
            UnitQuaternion::identity()
        };

        let prev_orientation = UnitQuaternion::new_normalize(NQuaternion::new(
            pose.pose.pose.orientation.w,
            pose.pose.pose.orientation.x,
            pose.pose.pose.orientation.y,
            pose.pose.pose.orientation.z,
        ));
        let curr_orientation = (prev_orientation * delta_orientation).into_inner();

        let mut pose_with_delay = pose.clone();
        pose_with_delay.header.timestamp = pose
            .header
            .timestamp
            .saturating_add((delay_time.max(0.0) * 1_000_000_000.0) as u64);
        pose_with_delay.pose.pose.orientation = Quaternion {
            x: curr_orientation.coords.x,
            y: curr_orientation.coords.y,
            z: curr_orientation.coords.z,
            w: curr_orientation.coords.w,
        };

        let (_roll, pitch, _yaw) = self.quaternion_to_rpy(pose_with_delay.pose.pose.orientation);
        let vx = self.kf.x_element(0, StateIndex::Vx as usize);
        pose_with_delay.pose.pose.position.z += vx * delay_time * sin(-pitch);

        pose_with_delay
    }

    fn update_simple_1d_filters(
        &mut self,
        pose: &PoseWithCovarianceStamped,
        smoothing_step: usize,
    ) {
        let z = pose.pose.pose.position.z;
        let (roll, pitch, _yaw) = self.quaternion_to_rpy(pose.pose.pose.orientation);

        let smoothing_step = smoothing_step as f64;
        let z_var = pose.pose.covariance[POSE_COV_Z_Z] * smoothing_step;
        let roll_var = pose.pose.covariance[POSE_COV_ROLL_ROLL] * smoothing_step;
        let pitch_var = pose.pose.covariance[POSE_COV_PITCH_PITCH] * smoothing_step;

        self.z_filter.update(z, z_var, self.ekf_dt);
        self.roll_filter.update(roll, roll_var, self.ekf_dt);
        self.pitch_filter.update(pitch, pitch_var, self.ekf_dt);
    }

    /// Fuses a (vx, wz) twist measurement using the message's own covariance and a
    /// Mahalanobis gate, matching upstream. Callers that want the "don't trust vx at low
    /// speed" behaviour must call `apply_twist_observability_gate` on `twist` first. This
    /// keeps running during MRM Dead Reckoning -- see the note on `measurement_update_pose`.
    pub fn measurement_update_twist(
        &mut self,
        twist: &TwistWithCovarianceStamped,
        t_curr: u64,
    ) -> bool {
        if twist.header.frame_id != "base_link" && self.twist_frame_id_warn.should_emit(t_curr) {
            log::warn!(
                "twist frame_id must be base_link, got {}",
                twist.header.frame_id
            );
        }

        self.last_angular_velocity = Vector3::zeros();

        let mut delay_time = nanos_to_seconds_delta(t_curr, twist.header.timestamp)
            + self.params.twist_additional_delay;
        if delay_time < 0.0 && self.twist_delay_time_warn.should_emit(t_curr) {
            log::warn!("[EKF] twist delay time is negative: {delay_time}. Treated as 0.");
        }
        delay_time = delay_time.max(0.0);

        let delay_step = self.find_closest_delay_time_index(delay_time);
        if delay_step >= self.params.extend_state_step {
            if self.twist_delay_step_warn.should_emit(t_curr) {
                log::warn!(
                    "[EKF] twist delay step {delay_step} exceeds extend_state_step {}. Ignoring measurement.",
                    self.params.extend_state_step
                );
            }
            return false;
        }

        let y = DVector::from_vec(vec![
            twist.twist.twist.linear.x,
            twist.twist.twist.angular.z,
        ]);
        if has_nan(&y) || has_inf(&y) {
            log::warn!("[EKF] twist measurement includes NaN or Inf. ignore update.");
            return false;
        }

        let y_ekf = DVector::from_vec(vec![
            self.kf.x_element(delay_step, StateIndex::Vx as usize),
            self.kf.x_element(delay_step, StateIndex::Wz as usize),
        ]);
        let p_curr = self.kf.latest_p();
        let p_y = p_curr.view((4, 4), (2, 2)).clone_owned();

        let distance = mahalanobis(&y_ekf, &y, &p_y);
        if distance > self.params.twist_gate_dist {
            if self.twist_mahalanobis_warn.should_emit(t_curr) {
                log::warn!(
                    "[EKF] twist Mahalanobis distance {distance} exceeds gate {}. Ignore the measurement data.",
                    self.params.twist_gate_dist
                );
            }
            return false;
        }

        let r = twist_measurement_covariance(
            &twist.twist.covariance,
            self.params.twist_smoothing_steps,
        );

        if !self
            .kf
            .update_with_delay(&y, &self.twist_measurement_matrix, &r, delay_step)
        {
            return false;
        }

        self.last_angular_velocity = Vector3::new(
            twist.twist.twist.angular.x,
            twist.twist.twist.angular.y,
            twist.twist.twist.angular.z,
        );

        true
    }

    /// Ages the delay-time buffer by one predict-tick: the just-predicted state becomes
    /// index 0 (age 0), and every older entry (which just got pushed back one slot in the
    /// kalman filter's extended state, see `kalman_filter::predict_with_delay`) gets `dt`
    /// added to its age. Must shift toward *higher* indices to stay aligned with how the
    /// extended state itself shifts.
    ///
    /// Matches upstream `EKFModule::accumulate_delay_time`: it is *not* called by
    /// `predict_with_delay`. Callers must call this once per predict tick, with the same
    /// `dt`, alongside `predict_with_delay(dt)` (see that method's doc comment).
    pub fn accumulate_delay_time(&mut self, dt: f64) {
        let len = self.accumulated_delay_times.len();
        if len == 0 {
            return;
        }

        for i in (1..len).rev() {
            self.accumulated_delay_times[i] = self.accumulated_delay_times[i - 1];
        }
        self.accumulated_delay_times[0] = 0.0;
        for time in self.accumulated_delay_times.iter_mut().skip(1) {
            *time += dt;
        }
    }

    pub fn find_closest_delay_time_index(&self, target_value: f64) -> usize {
        let len = self.accumulated_delay_times.len();
        if len == 0 {
            return 0;
        }

        if target_value > self.accumulated_delay_times[len - 1] {
            return len;
        }

        // Matches `std::lower_bound`'s semantics via an actual binary search (not a linear
        // scan): `partition_point` returns the index of the first entry >= target_value,
        // relying on `accumulated_delay_times` being kept sorted ascending by
        // `accumulate_delay_time`.
        let lower = self
            .accumulated_delay_times
            .partition_point(|&time| time < target_value);

        if lower == 0 {
            return 0;
        }
        if lower == len {
            return len - 1;
        }

        let prev = lower - 1;
        let diff_prev = target_value - self.accumulated_delay_times[prev];
        let diff_lower = self.accumulated_delay_times[lower] - target_value;
        if diff_prev < diff_lower {
            prev
        } else {
            lower
        }
    }

    /// Ported from `tf2::getYaw` (`ros2/geometry2`, `tf2/include/tf2/impl/utils.hpp`,
    /// `humble` branch) rather than `autoware_core` -- `tf2::getYaw` is a ROS 2 core
    /// library function, not an Autoware one. Unlike a plain
    /// `atan2(2*(w*z+x*y), 1-2*(y²+z²))`, tf2's version falls back to a different formula
    /// near the pitch = +/-90 deg gimbal-lock singularity (where yaw and roll become
    /// coupled and the "normal" formula loses precision), and normalizes by
    /// `sqx+sqy+sqz+sqw` instead of assuming an already-unit quaternion.
    fn quaternion_to_yaw(&self, q: Quaternion) -> f64 {
        let sqx = q.x * q.x;
        let sqy = q.y * q.y;
        let sqz = q.z * q.z;
        let sqw = q.w * q.w;

        let sarg = -2.0 * (q.x * q.z - q.w * q.y) / (sqx + sqy + sqz + sqw);

        if sarg <= -0.99999 {
            -2.0 * atan2(q.y, q.x)
        } else if sarg >= 0.99999 {
            2.0 * atan2(q.y, q.x)
        } else {
            atan2(2.0 * (q.x * q.y + q.w * q.z), sqw + sqx - sqy - sqz)
        }
    }

    /// Returns `(roll, pitch, yaw)` in radians (ZYX Euler convention). `autoware_utils_geometry`
    /// lives in the separate `autowarefoundation/autoware_utils` repo, not `autoware_core`;
    /// its `get_rpy` delegates entirely to `tf2::Matrix3x3(q).getRPY(...)`
    /// (`ros2/geometry2`, `tf2/include/tf2/LinearMath/Matrix3x3.hpp`, `humble` branch,
    /// `getEulerYPR`). That function's "normal case" formula is algebraically identical to
    /// the one below, but it also has an explicit gimbal-lock branch (pitch == +/-90 deg,
    /// where roll and yaw become coupled and only their sum/difference is defined) that a
    /// plain `asin` clamp does not reproduce -- ported here as the `m20.abs() >= 1.0`
    /// branch instead of clamping the `asin` argument.
    fn quaternion_to_rpy(&self, q: Quaternion) -> (f64, f64, f64) {
        // == tf2::Matrix3x3::setRotation's m_el[2].x() == -sin(pitch).
        let m20 = 2.0 * (q.x * q.z - q.w * q.y);

        if m20.abs() >= 1.0 {
            let delta = atan2(
                2.0 * (q.y * q.z + q.w * q.x),
                1.0 - 2.0 * (q.x * q.x + q.y * q.y),
            );
            let pitch = if m20 < 0.0 {
                core::f64::consts::FRAC_PI_2
            } else {
                -core::f64::consts::FRAC_PI_2
            };
            (delta, pitch, 0.0)
        } else {
            let sinr_cosp = 2.0 * (q.w * q.x + q.y * q.z);
            let cosr_cosp = 1.0 - 2.0 * (q.x * q.x + q.y * q.y);
            let roll = atan2(sinr_cosp, cosr_cosp);

            let pitch = libm::asin(-m20);

            let siny_cosp = 2.0 * (q.w * q.z + q.x * q.y);
            let cosy_cosp = 1.0 - 2.0 * (q.y * q.y + q.z * q.z);
            let yaw = atan2(siny_cosp, cosy_cosp);

            (roll, pitch, yaw)
        }
    }

    fn rpy_to_quaternion(&self, roll: f64, pitch: f64, yaw: f64) -> Quaternion {
        let cy = cos(yaw * 0.5);
        let sy = sin(yaw * 0.5);
        let cp = cos(pitch * 0.5);
        let sp = sin(pitch * 0.5);
        let cr = cos(roll * 0.5);
        let sr = sin(roll * 0.5);

        Quaternion {
            w: cr * cp * cy + sr * sp * sy,
            x: sr * cp * cy - cr * sp * sy,
            y: cr * sp * cy + sr * cp * sy,
            z: cr * cp * sy - sr * sp * cy,
        }
    }
}

// Subtracts in exact `u64` nanoseconds first, then converts to `f64`, instead of
// converting each side to `f64` before subtracting: realistic epoch nanosecond values
// (~1e18) already lose precision past `f64`'s 2^53 exact-integer range, but the
// difference itself (realistically well under a minute, i.e. ~1e9-1e10 ns) fits exactly.
// This also matches how `rclcpp::Time`/`Duration` work internally (nanoseconds kept as an
// integer until the final `.seconds()` conversion), which this crate has no equivalent of.
fn nanos_to_seconds_delta(t_curr: u64, t_prev: u64) -> f64 {
    if t_curr >= t_prev {
        (t_curr - t_prev) as f64 / 1_000_000_000.0
    } else {
        -((t_prev - t_curr) as f64) / 1_000_000_000.0
    }
}

/// Awkernel node-layer helper mirroring upstream `EKFLocalizer::callback_twist_with_covariance`:
/// below `threshold_observable_velocity_mps`, the vx observation is not trusted, so its
/// variance is inflated (the wz variance is untouched). Call this before
/// `EKFModule::measurement_update_twist`. A `threshold` of `0.0` disables the gate.
pub fn apply_twist_observability_gate(
    twist: &mut TwistWithCovarianceStamped,
    threshold_observable_velocity_mps: f64,
) {
    if twist.twist.twist.linear.x.abs() < threshold_observable_velocity_mps {
        twist.twist.covariance[0] = 10000.0;
    }
}

/// Stand-in for the node-layer ownership `EKFModule` doesn't have yet (upstream's
/// `EKFLocalizer` owns its `EKFModule` via `std::make_unique`, as a regular member). Once
/// DAG/pub-sub wiring gives this crate an equivalent task/node struct that owns an
/// `EKFModule` instance directly, callers should go through that instead of this lazily
/// initialized global singleton, and this function should be removed.
pub fn get_or_initialize_default_module() -> &'static mut EKFModule {
    let existing = EKF_MODULE_INSTANCE.load(AtomicOrdering::Acquire);
    if !existing.is_null() {
        return unsafe { &mut *existing };
    }

    let boxed = alloc::boxed::Box::new(EKFModule::new(EKFParameters::default()));
    let ptr = alloc::boxed::Box::into_raw(boxed);

    match EKF_MODULE_INSTANCE.compare_exchange(
        null_mut(),
        ptr,
        AtomicOrdering::AcqRel,
        AtomicOrdering::Acquire,
    ) {
        Ok(_) => unsafe { &mut *ptr },
        Err(existing_ptr) => unsafe {
            let _ = alloc::boxed::Box::from_raw(ptr);
            &mut *existing_ptr
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn identity_pose_stamped(timestamp: u64) -> PoseWithCovarianceStamped {
        pose_stamped_at(0.0, 0.0, 0.0, 0.0, timestamp)
    }

    fn pose_stamped_at(
        x: f64,
        y: f64,
        z: f64,
        yaw: f64,
        timestamp: u64,
    ) -> PoseWithCovarianceStamped {
        let mut covariance = [0.0; 36];
        covariance[POSE_COV_X_X] = 0.01;
        covariance[POSE_COV_Y_Y] = 0.01;
        covariance[POSE_COV_YAW_YAW] = 0.01;
        covariance[POSE_COV_Z_Z] = 0.01;
        covariance[POSE_COV_ROLL_ROLL] = 0.01;
        covariance[POSE_COV_PITCH_PITCH] = 0.01;

        PoseWithCovarianceStamped {
            header: common_types::Header {
                frame_id: "map",
                timestamp,
            },
            pose: PoseWithCovariance {
                pose: Pose {
                    position: Point3D { x, y, z },
                    orientation: Quaternion {
                        x: 0.0,
                        y: 0.0,
                        z: sin(yaw * 0.5),
                        w: cos(yaw * 0.5),
                    },
                },
                covariance,
            },
        }
    }

    fn twist_stamped_at(vx: f64, wz: f64, timestamp: u64) -> TwistWithCovarianceStamped {
        vehicle_velocity_converter::reactor_helpers::create_empty_twist(timestamp).apply(|t| {
            t.twist.twist.linear.x = vx;
            t.twist.twist.angular.z = wz;
            t.twist.covariance[0] = 0.04;
            t.twist.covariance[35] = 0.01;
        })
    }

    trait Apply {
        fn apply(self, f: impl FnOnce(&mut Self)) -> Self;
    }
    impl<T> Apply for T {
        fn apply(mut self, f: impl FnOnce(&mut Self)) -> Self {
            f(&mut self);
            self
        }
    }

    // [own test] no upstream equivalent.
    #[test]
    fn initialize_applies_tf_transform_and_message_covariance() {
        let mut ekf = EKFModule::new(EKFParameters::default());
        let mut pose = identity_pose_stamped(0);
        pose.pose.pose.position.x = 1.0;
        pose.pose.pose.position.y = 2.0;
        pose.pose.covariance[POSE_COV_X_X] = 0.02;
        pose.pose.covariance[POSE_COV_Y_Y] = 0.03;
        pose.pose.covariance[POSE_COV_YAW_YAW] = 0.04;

        // A 90 degree yaw transform: w=cos(45deg), z=sin(45deg).
        let mut transform = Transform::identity();
        transform.translation.x = 10.0;
        transform.translation.y = 20.0;
        transform.rotation.z = core::f64::consts::FRAC_1_SQRT_2;
        transform.rotation.w = core::f64::consts::FRAC_1_SQRT_2;

        ekf.initialize(&pose, &transform);

        let p = ekf.get_current_pose(true, 0);
        assert!((p.pose.position.x - 11.0).abs() < 1e-9);
        assert!((p.pose.position.y - 22.0).abs() < 1e-9);

        // The 90 degree yaw transform should show up directly in the returned orientation
        // (pose itself has yaw=0, so biased_yaw = 0 + 90deg == the transform's own rotation).
        assert!((p.pose.orientation.z - core::f64::consts::FRAC_1_SQRT_2).abs() < 1e-9);
        assert!((p.pose.orientation.w - core::f64::consts::FRAC_1_SQRT_2).abs() < 1e-9);
        assert!(p.pose.orientation.x.abs() < 1e-9);
        assert!(p.pose.orientation.y.abs() < 1e-9);

        let cov = ekf.get_current_pose_covariance();
        assert_eq!(cov[POSE_COV_X_X], 0.02);
        assert_eq!(cov[POSE_COV_Y_Y], 0.03);
        assert_eq!(cov[POSE_COV_YAW_YAW], 0.04);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn measurement_update_pose_moves_state_toward_measurement() {
        let mut ekf = EKFModule::new(EKFParameters::default());
        ekf.initialize(&identity_pose_stamped(0), &Transform::identity());

        let pose = pose_stamped_at(1.0, 0.0, 0.0, 0.0, 0);
        let accepted = ekf.measurement_update_pose(&pose, 0);
        assert!(accepted);
        assert!(ekf.get_current_pose(false, 0).pose.position.x > 0.0);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn measurement_update_pose_rejects_excessive_delay() {
        let mut params = EKFParameters::default();
        params.extend_state_step = 3;
        let mut ekf = EKFModule::new(params);
        ekf.initialize(&identity_pose_stamped(0), &Transform::identity());

        for _ in 0..3 {
            // Mirrors upstream: the node calls both once per tick with the same dt.
            ekf.accumulate_delay_time(0.1);
            ekf.predict_with_delay(0.1);
        }

        let before = ekf.get_current_pose(false, 0).pose.position.x;
        let pose = pose_stamped_at(1.0, 0.0, 0.0, 0.0, 0);
        // 10 seconds of delay is far beyond the ~0.3s of history the buffer holds.
        let accepted = ekf.measurement_update_pose(&pose, 10_000_000_000);
        assert!(!accepted);
        assert_eq!(ekf.get_current_pose(false, 0).pose.position.x, before);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn measurement_update_pose_rejects_mahalanobis_outlier() {
        let mut ekf = EKFModule::new(EKFParameters::default());
        ekf.initialize(&identity_pose_stamped(0), &Transform::identity());

        let before = ekf.get_current_pose(false, 0).pose.position.x;
        let pose = pose_stamped_at(1000.0, 0.0, 0.0, 0.0, 0);
        let accepted = ekf.measurement_update_pose(&pose, 0);
        assert!(!accepted);
        assert_eq!(ekf.get_current_pose(false, 0).pose.position.x, before);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn measurement_update_pose_rejects_nan() {
        let mut ekf = EKFModule::new(EKFParameters::default());
        ekf.initialize(&identity_pose_stamped(0), &Transform::identity());

        let mut pose = pose_stamped_at(1.0, 0.0, 0.0, 0.0, 0);
        pose.pose.pose.position.x = f64::NAN;
        assert!(!ekf.measurement_update_pose(&pose, 0));
    }

    // [own test] no upstream equivalent. Also serves as a regression guard for the
    // MRM/Dead Reckoning design: `EKFModule` has no "MRM mode" of its own (see the note
    // on `measurement_update_pose`), so this must keep working via
    // `measurement_update_twist` alone even though no pose update has ever been applied
    // in this test.
    #[test]
    fn measurement_update_twist_moves_state_toward_measurement() {
        let mut ekf = EKFModule::new(EKFParameters::default());
        ekf.initialize(&identity_pose_stamped(0), &Transform::identity());

        let twist = twist_stamped_at(2.0, 0.0, 0);
        assert!(ekf.measurement_update_twist(&twist, 0));
        assert!(ekf.get_current_twist(0).twist.linear.x > 0.0);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn measurement_update_twist_rejects_mahalanobis_outlier() {
        let mut ekf = EKFModule::new(EKFParameters::default());
        ekf.initialize(&identity_pose_stamped(0), &Transform::identity());

        let before = ekf.get_current_twist(0).twist.linear.x;
        let twist = twist_stamped_at(1000.0, 0.0, 0);
        assert!(!ekf.measurement_update_twist(&twist, 0));
        assert_eq!(ekf.get_current_twist(0).twist.linear.x, before);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn apply_twist_observability_gate_inflates_low_speed_variance_only() {
        let mut low_speed = twist_stamped_at(0.01, 0.5, 0);
        apply_twist_observability_gate(&mut low_speed, 0.05);
        assert_eq!(low_speed.twist.covariance[0], 10000.0);
        assert_ne!(low_speed.twist.covariance[35], 10000.0);

        let mut normal_speed = twist_stamped_at(5.0, 0.5, 0);
        let original_vx_var = normal_speed.twist.covariance[0];
        apply_twist_observability_gate(&mut normal_speed, 0.05);
        assert_eq!(normal_speed.twist.covariance[0], original_vx_var);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn apply_twist_observability_gate_suppresses_low_speed_correction() {
        let mut gated_ekf = EKFModule::new(EKFParameters::default());
        gated_ekf.initialize(&identity_pose_stamped(0), &Transform::identity());
        let mut ungated_ekf = EKFModule::new(EKFParameters::default());
        ungated_ekf.initialize(&identity_pose_stamped(0), &Transform::identity());

        let mut gated_twist = twist_stamped_at(0.01, 0.0, 0);
        apply_twist_observability_gate(&mut gated_twist, 0.05);
        let ungated_twist = twist_stamped_at(0.01, 0.0, 0);

        gated_ekf.measurement_update_twist(&gated_twist, 0);
        ungated_ekf.measurement_update_twist(&ungated_twist, 0);

        assert!(
            gated_ekf.get_current_twist(0).twist.linear.x
                < ungated_ekf.get_current_twist(0).twist.linear.x
        );
    }

    // [own test] no upstream equivalent.
    #[test]
    fn find_closest_delay_time_index_prefers_upper_bound_on_exact_tie() {
        let mut ekf = EKFModule::new(EKFParameters::default());
        // Force a known, small buffer: [0.0, 1.0, 2.0].
        ekf.accumulated_delay_times = alloc::vec![0.0, 1.0, 2.0];
        // Exactly halfway between index 0 (0.0) and index 1 (1.0): upstream's
        // lower_bound-based tie-break prefers the upper (later) index.
        assert_eq!(ekf.find_closest_delay_time_index(0.5), 1);
        assert_eq!(ekf.find_closest_delay_time_index(0.0), 0);
        assert_eq!(ekf.find_closest_delay_time_index(2.0), 2);
        assert_eq!(ekf.find_closest_delay_time_index(2.1), 3);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn accumulate_delay_time_tracks_block_age_in_ascending_order() {
        let mut ekf = EKFModule::new(EKFParameters::default());
        ekf.accumulated_delay_times = alloc::vec![1e15; 4];

        ekf.accumulate_delay_time(0.1);
        assert_eq!(ekf.accumulated_delay_times[0], 0.0);

        ekf.accumulate_delay_time(0.1);
        assert_eq!(ekf.accumulated_delay_times[0], 0.0);
        assert!((ekf.accumulated_delay_times[1] - 0.1).abs() < 1e-12);

        ekf.accumulate_delay_time(0.1);
        assert_eq!(ekf.accumulated_delay_times[0], 0.0);
        assert!((ekf.accumulated_delay_times[1] - 0.1).abs() < 1e-12);
        assert!((ekf.accumulated_delay_times[2] - 0.2).abs() < 1e-12);

        // Ages are monotonically non-decreasing: block 0 is always "now".
        for pair in ekf.accumulated_delay_times.windows(2) {
            assert!(pair[0] <= pair[1]);
        }
    }

    /// [own test] no upstream equivalent. `predict_with_delay` must not touch the
    /// delay-time buffer, matching upstream where
    /// `EKFModule::predict_with_delay` and `EKFModule::accumulate_delay_time` are two
    /// separate calls made by the node (`update_predict_frequency` vs. `timer_callback`'s
    /// prediction block). If `predict_with_delay` called `accumulate_delay_time`
    /// internally, a caller that (correctly, per upstream) also calls
    /// `accumulate_delay_time` itself would age the buffer twice per tick.
    #[test]
    fn predict_with_delay_does_not_age_the_delay_time_buffer() {
        let mut ekf = EKFModule::new(EKFParameters::default());
        let before = ekf.accumulated_delay_times.clone();

        ekf.predict_with_delay(0.1);

        assert_eq!(ekf.accumulated_delay_times, before);
    }

    /// [own test] no upstream equivalent. `EKFParameters::default()` must track
    /// upstream's shipped `config/ekf_localizer.param.yaml` (autoware_core 1.8.0)
    /// field-for-field.
    #[test]
    fn default_parameters_match_upstream_shipped_yaml() {
        let p = EKFParameters::default();
        assert!(p.enable_yaw_bias_estimation);
        assert_eq!(p.extend_state_step, 50);
        assert_eq!(p.proc_stddev_vx_c, 10.0);
        assert_eq!(p.proc_stddev_wz_c, 5.0);
        assert_eq!(p.proc_stddev_yaw_c, 0.005);
        assert_eq!(p.z_filter_proc_dev, 5.0);
        assert_eq!(p.roll_filter_proc_dev, 0.1);
        assert_eq!(p.pitch_filter_proc_dev, 0.1);
        assert_eq!(p.pose_frame_id, "map");
        assert_eq!(p.pose_additional_delay, 0.0);
        assert_eq!(p.pose_gate_dist, 49.5);
        assert_eq!(p.pose_smoothing_steps, 5);
        assert_eq!(p.twist_additional_delay, 0.0);
        assert_eq!(p.twist_gate_dist, 46.1);
        assert_eq!(p.twist_smoothing_steps, 2);
        assert_eq!(p.threshold_observable_velocity_mps, 0.0);
    }
}
