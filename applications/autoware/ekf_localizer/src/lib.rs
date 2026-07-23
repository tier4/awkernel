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
// original file path: localization/autoware_ekf_localizer/src/ekf_localizer.cpp
// test code: localization/autoware_ekf_localizer/test/test_ekf_module.cpp
// version: 1.8.0

#![no_std]
#![allow(non_snake_case)]

extern crate alloc;

use alloc::{vec, vec::Vec};
pub use common_types::Header;
use core::ptr::null_mut;
use core::sync::atomic::{AtomicPtr, Ordering as AtomicOrdering};
use libm::{atan2, cos, sin};
use nalgebra::{Matrix6, Vector3, Vector6};
pub use vehicle_velocity_converter::TwistWithCovariance;

static EKF_MODULE_INSTANCE: AtomicPtr<EKFModule> = AtomicPtr::new(null_mut());

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

#[derive(Debug, Clone, Copy)]
pub struct Twist {
    pub linear: Vector3<f64>,
    pub angular: Vector3<f64>,
}

#[derive(Debug, Clone, Copy)]
pub struct PoseWithCovariance {
    pub pose: Pose,
    pub covariance: [f64; 36],
}

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
}

impl Default for EKFParameters {
    fn default() -> Self {
        Self {
            enable_yaw_bias_estimation: true,
            extend_state_step: 50,
            proc_stddev_vx_c: 2.0,
            proc_stddev_wz_c: 1.0,
            proc_stddev_yaw_c: 0.005,
            z_filter_proc_dev: 1.0,
            roll_filter_proc_dev: 0.1,
            pitch_filter_proc_dev: 0.1,
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
        self.var = self.var + proc_var_x_d;

        let kalman_gain = self.var / (self.var + obs_var);
        self.x = self.x + kalman_gain * (obs - self.x);
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

#[derive(Debug, Clone)]
pub struct EKFModule {
    params: EKFParameters,
    state: StateVector,
    covariance: StateCovariance,
    z_filter: Simple1DFilter,
    roll_filter: Simple1DFilter,
    pitch_filter: Simple1DFilter,
    accumulated_delay_times: Vec<f64>,
    // When true, only prediction is performed (no measurement updates)
    is_mrm_mode: bool,
}

impl EKFModule {
    pub fn new(params: EKFParameters) -> Self {
        let state = StateVector::zeros();
        let mut covariance = StateCovariance::identity() * 1e15;

        covariance[(StateIndex::Yaw as usize, StateIndex::Yaw as usize)] = 50.0;
        if params.enable_yaw_bias_estimation {
            covariance[(StateIndex::YawBias as usize, StateIndex::YawBias as usize)] = 50.0;
        }
        covariance[(StateIndex::Vx as usize, StateIndex::Vx as usize)] = 1000.0;
        covariance[(StateIndex::Wz as usize, StateIndex::Wz as usize)] = 50.0;

        let mut z_filter = Simple1DFilter::new();
        let mut roll_filter = Simple1DFilter::new();
        let mut pitch_filter = Simple1DFilter::new();

        z_filter.set_proc_var(params.z_filter_proc_dev * params.z_filter_proc_dev);
        roll_filter.set_proc_var(params.roll_filter_proc_dev * params.roll_filter_proc_dev);
        pitch_filter.set_proc_var(params.pitch_filter_proc_dev * params.pitch_filter_proc_dev);

        let accumulated_delay_times = vec![1e15; params.extend_state_step];

        Self {
            params,
            state,
            covariance,
            z_filter,
            roll_filter,
            pitch_filter,
            accumulated_delay_times,
            is_mrm_mode: false,
        }
    }

    pub fn initialize(&mut self, initial_pose: Pose) {
        self.state[StateIndex::X as usize] = initial_pose.position.x;
        self.state[StateIndex::Y as usize] = initial_pose.position.y;
        self.state[StateIndex::Yaw as usize] = self.quaternion_to_yaw(initial_pose.orientation);
        self.state[StateIndex::YawBias as usize] = 0.0;
        self.state[StateIndex::Vx as usize] = 0.0;
        self.state[StateIndex::Wz as usize] = 0.0;

        self.covariance = StateCovariance::identity() * 0.01;
        if self.params.enable_yaw_bias_estimation {
            self.covariance[(StateIndex::YawBias as usize, StateIndex::YawBias as usize)] = 0.0001;
        }

        self.z_filter.init(initial_pose.position.z, 0.01);
        self.roll_filter.init(0.0, 0.01);
        self.pitch_filter.init(0.0, 0.01);
    }

    fn predict_next_state(&self, dt: f64) -> StateVector {
        let mut x_next = self.state.clone();
        let x = self.state[StateIndex::X as usize];
        let y = self.state[StateIndex::Y as usize];
        let yaw = self.state[StateIndex::Yaw as usize];
        let yaw_bias = self.state[StateIndex::YawBias as usize];
        let vx = self.state[StateIndex::Vx as usize];
        let wz = self.state[StateIndex::Wz as usize];

        x_next[StateIndex::X as usize] = x + vx * cos(yaw + yaw_bias) * dt;
        x_next[StateIndex::Y as usize] = y + vx * sin(yaw + yaw_bias) * dt;
        let yaw_next = yaw + wz * dt;
        x_next[StateIndex::Yaw as usize] = atan2(sin(yaw_next), cos(yaw_next));
        x_next[StateIndex::YawBias as usize] = yaw_bias;
        x_next[StateIndex::Vx as usize] = vx;
        x_next[StateIndex::Wz as usize] = wz;

        x_next
    }

    fn create_state_transition_matrix(&self, dt: f64) -> Matrix6<f64> {
        let mut F = Matrix6::identity();
        let yaw = self.state[StateIndex::Yaw as usize];
        let yaw_bias = self.state[StateIndex::YawBias as usize];
        let vx = self.state[StateIndex::Vx as usize];

        F[(StateIndex::X as usize, StateIndex::Yaw as usize)] = -vx * sin(yaw + yaw_bias) * dt;
        F[(StateIndex::X as usize, StateIndex::YawBias as usize)] = -vx * sin(yaw + yaw_bias) * dt;
        F[(StateIndex::X as usize, StateIndex::Vx as usize)] = cos(yaw + yaw_bias) * dt;

        F[(StateIndex::Y as usize, StateIndex::Yaw as usize)] = vx * cos(yaw + yaw_bias) * dt;
        F[(StateIndex::Y as usize, StateIndex::YawBias as usize)] = vx * cos(yaw + yaw_bias) * dt;
        F[(StateIndex::Y as usize, StateIndex::Vx as usize)] = sin(yaw + yaw_bias) * dt;

        F[(StateIndex::Yaw as usize, StateIndex::Wz as usize)] = dt;

        F
    }

    fn process_noise_covariance(&self, dt: f64) -> Matrix6<f64> {
        let mut Q = Matrix6::zeros();

        Q[(StateIndex::Vx as usize, StateIndex::Vx as usize)] =
            self.params.proc_stddev_vx_c * self.params.proc_stddev_vx_c * dt * dt;
        Q[(StateIndex::Wz as usize, StateIndex::Wz as usize)] =
            self.params.proc_stddev_wz_c * self.params.proc_stddev_wz_c * dt * dt;
        Q[(StateIndex::Yaw as usize, StateIndex::Yaw as usize)] =
            self.params.proc_stddev_yaw_c * self.params.proc_stddev_yaw_c * dt * dt;

        Q[(StateIndex::X as usize, StateIndex::X as usize)] = 0.0;
        Q[(StateIndex::Y as usize, StateIndex::Y as usize)] = 0.0;
        Q[(StateIndex::YawBias as usize, StateIndex::YawBias as usize)] = 0.0;

        Q
    }

    pub fn predict(&mut self, dt: f64) {
        self.state = self.predict_next_state(dt);
        let F = self.create_state_transition_matrix(dt);
        let Q = self.process_noise_covariance(dt);
        self.covariance = F * self.covariance * F.transpose() + Q;
        self.accumulate_delay_time(dt);
    }

    pub fn predict_with_delay(&mut self, dt: f64) {
        self.predict(dt);
    }

    pub fn predict_only(&mut self, dt: f64) {
        self.predict(dt);
    }

    pub fn get_current_pose(&self, get_biased_yaw: bool) -> Pose {
        let z = self.z_filter.get_x();
        let roll = self.roll_filter.get_x();
        let pitch = self.pitch_filter.get_x();

        let x = self.state[StateIndex::X as usize];
        let y = self.state[StateIndex::Y as usize];
        let biased_yaw = self.state[StateIndex::Yaw as usize];
        let yaw_bias = self.state[StateIndex::YawBias as usize];

        let yaw = if get_biased_yaw {
            biased_yaw
        } else {
            biased_yaw + yaw_bias
        };

        Pose {
            position: Point3D { x, y, z },
            orientation: self.rpy_to_quaternion(roll, pitch, yaw),
        }
    }

    pub fn get_current_twist(&self) -> Twist {
        let vx = self.state[StateIndex::Vx as usize];
        let wz = self.state[StateIndex::Wz as usize];

        Twist {
            linear: Vector3::new(vx, 0.0, 0.0),
            angular: Vector3::new(0.0, 0.0, wz),
        }
    }

    pub fn get_yaw_bias(&self) -> f64 {
        self.state[StateIndex::YawBias as usize]
    }

    pub fn get_current_pose_with_covariance(&self) -> PoseWithCovariance {
        let pose = self.get_current_pose(false);
        let pose_covariance = self.get_current_pose_covariance();
        PoseWithCovariance {
            pose,
            covariance: pose_covariance,
        }
    }

    pub fn get_current_pose_covariance(&self) -> [f64; 36] {
        let mut cov = [0.0; 36];

        for i in 0..6 {
            for j in 0..6 {
                cov[i * 6 + j] = self.covariance[(i, j)];
            }
        }

        cov[14] = self.z_filter.get_var();
        cov[21] = self.roll_filter.get_var();
        cov[28] = self.pitch_filter.get_var();

        cov
    }

    pub fn get_current_twist_covariance(&self) -> [f64; 36] {
        let mut cov = [0.0; 36];

        cov[0] = self.covariance[(StateIndex::Vx as usize, StateIndex::Vx as usize)];
        cov[35] = self.covariance[(StateIndex::Wz as usize, StateIndex::Wz as usize)];

        cov
    }

    pub fn update_velocity(&mut self, vx_measurement: f64, wz_measurement: f64) {
        if self.is_mrm_mode {
            return;
        }

        let vx_obs_var = 1.0;
        let wz_obs_var = 0.1;

        let vx_var = self.covariance[(StateIndex::Vx as usize, StateIndex::Vx as usize)];
        let vx_gain = vx_var / (vx_var + vx_obs_var);
        self.state[StateIndex::Vx as usize] = self.state[StateIndex::Vx as usize]
            + vx_gain * (vx_measurement - self.state[StateIndex::Vx as usize]);
        self.covariance[(StateIndex::Vx as usize, StateIndex::Vx as usize)] =
            (1.0 - vx_gain) * vx_var;

        let wz_var = self.covariance[(StateIndex::Wz as usize, StateIndex::Wz as usize)];
        let wz_gain = wz_var / (wz_var + wz_obs_var);
        self.state[StateIndex::Wz as usize] = self.state[StateIndex::Wz as usize]
            + wz_gain * (wz_measurement - self.state[StateIndex::Wz as usize]);
        self.covariance[(StateIndex::Wz as usize, StateIndex::Wz as usize)] =
            (1.0 - wz_gain) * wz_var;
    }

    pub fn set_mrm_mode(&mut self, is_mrm: bool) {
        self.is_mrm_mode = is_mrm;
    }

    pub fn is_mrm(&self) -> bool {
        self.is_mrm_mode
    }

    pub fn accumulate_delay_time(&mut self, dt: f64) {
        let len = self.accumulated_delay_times.len();
        if len == 0 {
            return;
        }

        let last_time = self.accumulated_delay_times[len - 1];
        let new_time = last_time + dt;

        for i in 0..len - 1 {
            self.accumulated_delay_times[i] = self.accumulated_delay_times[i + 1];
        }
        self.accumulated_delay_times[len - 1] = new_time;
    }

    pub fn find_closest_delay_time_index(&self, target_value: f64) -> usize {
        let len = self.accumulated_delay_times.len();
        if len == 0 {
            return 0;
        }

        if target_value > self.accumulated_delay_times[len - 1] {
            return len;
        }

        let mut closest_index = 0;
        let mut min_diff = f64::MAX;

        for i in 0..len {
            let time = self.accumulated_delay_times[i];
            let diff = (target_value - time).abs();
            if diff < min_diff {
                min_diff = diff;
                closest_index = i;
            }
        }

        closest_index
    }

    fn quaternion_to_yaw(&self, q: Quaternion) -> f64 {
        atan2(
            2.0 * (q.w * q.z + q.x * q.y),
            1.0 - 2.0 * (q.y * q.y + q.z * q.z),
        )
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
    use core::f64::consts::PI;
    use nalgebra::{Matrix6, Vector6};

    #[test]
    fn predict_next_state_matches_formula() {
        let params = EKFParameters::default();
        let mut ekf = EKFModule::new(params);

        let x_curr = Vector6::new(2.0, 3.0, PI / 2.0, PI / 4.0, 10.0, 2.0 * PI / 3.0);

        ekf.state = x_curr.clone();

        let dt = 0.5;
        let x_next = ekf.predict_next_state(dt);

        let tol = 1e-10;
        assert!((x_next[0] - (2.0 + 10.0 * (PI / 2.0 + PI / 4.0).cos() * dt)).abs() < tol);
        assert!((x_next[1] - (3.0 + 10.0 * (PI / 2.0 + PI / 4.0).sin() * dt)).abs() < tol);
        let yaw_next = PI / 2.0 + (2.0 * PI / 3.0) * dt;
        let expected_yaw = yaw_next.sin().atan2(yaw_next.cos());
        assert!((x_next[2] - expected_yaw).abs() < 1e-6);
        assert!((x_next[3] - x_curr[3]).abs() < tol);
        assert!((x_next[4] - x_curr[4]).abs() < tol);
        assert!((x_next[5] - x_curr[5]).abs() < tol);
    }

    #[test]
    fn create_state_transition_matrix_numeric_approximation() {
        let params = EKFParameters::default();
        let mut ekf = EKFModule::new(params);

        // check around zero
        let dt = 0.1;
        let dx = Vector6::from_element(0.1);
        let x = Vector6::zeros();

        ekf.state = x.clone();
        let a = ekf.create_state_transition_matrix(dt);

        ekf.state = x.clone() + dx.clone();
        let x1 = ekf.predict_next_state(dt);
        ekf.state = x.clone();
        let x0 = ekf.predict_next_state(dt);
        let df = x1 - x0;

        {
            let mut s = 0.0;
            let v = df - a * dx;
            for i in 0..6 {
                let val = v[i];
                s += val * val;
            }
            assert!(s.sqrt() < 2e-3);
        }

        // check around a non-zero state
        let dx = Vector6::from_element(0.1);
        let x = Vector6::new(0.1, 0.2, 0.1, 0.4, 0.1, 0.3);

        ekf.state = x.clone();
        let a = ekf.create_state_transition_matrix(dt);

        ekf.state = x.clone() + dx.clone();
        let x1 = ekf.predict_next_state(dt);
        ekf.state = x.clone();
        let x0 = ekf.predict_next_state(dt);
        let df = x1 - x0;

        {
            let mut s = 0.0;
            let v = df - a * dx;
            for i in 0..6 {
                let val = v[i];
                s += val * val;
            }
            assert!(s.sqrt() < 5e-3);
        }
    }

    #[test]
    fn process_noise_covariance_values() {
        let mut params = EKFParameters::default();
        params.proc_stddev_yaw_c = 1.0;
        params.proc_stddev_vx_c = 2.0;
        params.proc_stddev_wz_c = 3.0;

        let ekf = EKFModule::new(params);

        let q = ekf.process_noise_covariance(1.0);

        // indices: yaw = 2, vx = 4, wz = 5
        assert!((q[(2, 2)] - 1.0_f64.powi(2)).abs() < 1e-12);
        assert!((q[(4, 4)] - 2.0_f64.powi(2)).abs() < 1e-12);
        assert!((q[(5, 5)] - 3.0_f64.powi(2)).abs() < 1e-12);

        // zero case
        let mut params = EKFParameters::default();
        params.proc_stddev_yaw_c = 0.0;
        params.proc_stddev_vx_c = 0.0;
        params.proc_stddev_wz_c = 0.0;
        let ekf2 = EKFModule::new(params);
        let q2 = ekf2.process_noise_covariance(1.0);
        {
            let mut s = 0.0;
            for i in 0..6 {
                for j in 0..6 {
                    let val = q2[(i, j)];
                    s += val * val;
                }
            }
            assert!(s == 0.0);
        }
    }

    #[test]
    fn pose_and_twist_covariance_mapping() {
        let params = EKFParameters::default();
        let mut ekf = EKFModule::new(params);

        // prepare a covariance matrix with top-left 3x3 = 1..9
        let mut p = Matrix6::<f64>::zeros();
        p[(0, 0)] = 1.0;
        p[(0, 1)] = 2.0;
        p[(0, 2)] = 3.0;
        p[(1, 0)] = 4.0;
        p[(1, 1)] = 5.0;
        p[(1, 2)] = 6.0;
        p[(2, 0)] = 7.0;
        p[(2, 1)] = 8.0;
        p[(2, 2)] = 9.0;

        ekf.covariance = p;

        // override the filter variances so those indices are replaced
        ekf.z_filter.var = 100.0;
        ekf.roll_filter.var = 200.0;
        ekf.pitch_filter.var = 300.0;

        let cov = ekf.get_current_pose_covariance();

        // check a few mapped entries according to get_current_pose_covariance implementation
        assert_eq!(cov[0], 1.0);
        assert_eq!(cov[1], 2.0);
        assert_eq!(cov[2], 3.0);
        assert_eq!(cov[6], 4.0);
        assert_eq!(cov[7], 5.0);
        assert_eq!(cov[8], 6.0);
        assert_eq!(cov[12], 7.0);
        assert_eq!(cov[13], 8.0);
        // index 14 is overwritten by z_filter.var
        assert_eq!(cov[14], 100.0);

        // twist covariance mapping (Vx -> index 0, Wz -> index 35)
        let mut p2 = Matrix6::<f64>::zeros();
        p2[(4, 4)] = 1.0;
        p2[(4, 5)] = 2.0;
        p2[(5, 4)] = 3.0;
        p2[(5, 5)] = 4.0;
        ekf.covariance = p2;

        let tcov = ekf.get_current_twist_covariance();
        assert_eq!(tcov[0], 1.0);
        assert_eq!(tcov[35], 4.0);
    }
}
