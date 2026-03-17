#![no_std]
#![allow(non_snake_case)]

extern crate alloc;

use core::f64::consts::PI;
use alloc::{vec, vec::Vec};
use nalgebra::{Matrix6, Vector6, Vector3};
use libm::{sin, cos, atan2, asin};

/// State indices for EKF
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StateIndex {
    X = 0,
    Y = 1,
    Yaw = 2,
    YawBias = 3,
    Vx = 4,
    Wz = 5,
}

/// EKF State vector (6x1)
/// [x, y, yaw, yaw_bias, vx, wz]
pub type StateVector = Vector6<f64>;

/// EKF Covariance matrix (6x6)
pub type StateCovariance = Matrix6<f64>;

/// 3D Point structure
#[derive(Debug, Clone, Copy)]
pub struct Point3D {
    pub x: f64,
    pub y: f64,
    pub z: f64,
}

/// Quaternion structure
#[derive(Debug, Clone, Copy)]
pub struct Quaternion {
    pub x: f64,
    pub y: f64,
    pub z: f64,
    pub w: f64,
}

/// Pose structure
#[derive(Debug, Clone, Copy)]
pub struct Pose {
    pub position: Point3D,
    pub orientation: Quaternion,
}

/// Twist structure
#[derive(Debug, Clone, Copy)]
pub struct Twist {
    pub linear: Vector3<f64>,
    pub angular: Vector3<f64>,
}

/// PoseWithCovariance structure
#[derive(Debug, Clone, Copy)]
pub struct PoseWithCovariance {
    pub pose: Pose,
    pub covariance: [f64; 36],
}

/// EKF Parameters
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

/// Simple 1D Filter for z, roll, pitch
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

        // Prediction step
        let proc_var_x_d = self.proc_var_x_c * dt * dt;
        self.var = self.var + proc_var_x_d;

        // Update step
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

/// Main EKF Module
#[derive(Debug, Clone)]
pub struct EKFModule {
    params: EKFParameters,
    dim_x: usize,
    state: StateVector,
    covariance: StateCovariance,
    z_filter: Simple1DFilter,
    roll_filter: Simple1DFilter,
    pitch_filter: Simple1DFilter,
    accumulated_delay_times: Vec<f64>,
    last_angular_velocity: Vector3<f64>,
    /// MRM (Minimal Risk Maneuver) mode flag
    /// When true, only prediction is performed (no measurement updates)
    is_mrm_mode: bool,
}

impl EKFModule {
    pub fn new(params: EKFParameters) -> Self {
        let dim_x = 6;
        let mut state = StateVector::zeros();
        let mut covariance = StateCovariance::identity() * 1e15;
        
        // Initialize covariance with reasonable values
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
            dim_x,
            state,
            covariance,
            z_filter,
            roll_filter,
            pitch_filter,
            accumulated_delay_times,
            last_angular_velocity: Vector3::zeros(),
            is_mrm_mode: false,
        }
    }

    /// Initialize EKF with initial pose
    pub fn initialize(&mut self, initial_pose: Pose) {
        // Set initial state directly from pose
        self.state[StateIndex::X as usize] = initial_pose.position.x;
        self.state[StateIndex::Y as usize] = initial_pose.position.y;
        self.state[StateIndex::Yaw as usize] = self.quaternion_to_yaw(initial_pose.orientation);
        self.state[StateIndex::YawBias as usize] = 0.0;
        self.state[StateIndex::Vx as usize] = 0.0;
        self.state[StateIndex::Wz as usize] = 0.0;

        // Initialize covariance (simplified)
        self.covariance = StateCovariance::identity() * 0.01;
        if self.params.enable_yaw_bias_estimation {
            self.covariance[(StateIndex::YawBias as usize, StateIndex::YawBias as usize)] = 0.0001;
        }

        // Initialize filters
        self.z_filter.init(initial_pose.position.z, 0.01);
        self.roll_filter.init(0.0, 0.01);
        self.pitch_filter.init(0.0, 0.01);
    }

    /// Predict next state using nonlinear state transition (core prediction logic)
    /// x_{k+1} = x_k + vx * cos(yaw + bias) * dt, y_{k+1} = y_k + vx * sin(yaw + bias) * dt, etc.
    fn predict_next_state(&self, dt: f64) -> StateVector {
        let mut x_next = self.state.clone();
        let x = self.state[StateIndex::X as usize];
        let y = self.state[StateIndex::Y as usize];
        let yaw = self.state[StateIndex::Yaw as usize];
        let yaw_bias = self.state[StateIndex::YawBias as usize];
        let vx = self.state[StateIndex::Vx as usize];
        let wz = self.state[StateIndex::Wz as usize];

        // Nonlinear state transition
        x_next[StateIndex::X as usize] = x + vx * cos(yaw + yaw_bias) * dt;
        x_next[StateIndex::Y as usize] = y + vx * sin(yaw + yaw_bias) * dt;
        // Normalize yaw to [-π, π] range (Autoware compatible)
        let yaw_next = yaw + wz * dt;
        x_next[StateIndex::Yaw as usize] = atan2(sin(yaw_next), cos(yaw_next));
        x_next[StateIndex::YawBias as usize] = yaw_bias;  // yaw bias doesn't change
        x_next[StateIndex::Vx as usize] = vx;  // velocity doesn't change in predict
        x_next[StateIndex::Wz as usize] = wz;  // angular velocity doesn't change in predict

        x_next
    }

    /// Create state transition (Jacobian) matrix F
    /// F = d(f)/d(x) where f is the nonlinear state transition function
    fn create_state_transition_matrix(&self, dt: f64) -> Matrix6<f64> {
        let mut F = Matrix6::identity();
        let yaw = self.state[StateIndex::Yaw as usize];
        let yaw_bias = self.state[StateIndex::YawBias as usize];
        let vx = self.state[StateIndex::Vx as usize];

        // Jacobian of position with respect to yaw and velocity
        F[(StateIndex::X as usize, StateIndex::Yaw as usize)] = -vx * sin(yaw + yaw_bias) * dt;
        F[(StateIndex::X as usize, StateIndex::YawBias as usize)] = -vx * sin(yaw + yaw_bias) * dt;
        F[(StateIndex::X as usize, StateIndex::Vx as usize)] = cos(yaw + yaw_bias) * dt;
        
        F[(StateIndex::Y as usize, StateIndex::Yaw as usize)] = vx * cos(yaw + yaw_bias) * dt;
        F[(StateIndex::Y as usize, StateIndex::YawBias as usize)] = vx * cos(yaw + yaw_bias) * dt;
        F[(StateIndex::Y as usize, StateIndex::Vx as usize)] = sin(yaw + yaw_bias) * dt;
        
        F[(StateIndex::Yaw as usize, StateIndex::Wz as usize)] = dt;

        F
    }

    /// Calculate process noise covariance Q
    /// Q represents the uncertainty in the motion model
    fn process_noise_covariance(&self, dt: f64) -> Matrix6<f64> {
        let mut Q = Matrix6::zeros();
        
        // Process noise for each state variable
        Q[(StateIndex::Vx as usize, StateIndex::Vx as usize)] = 
            self.params.proc_stddev_vx_c * self.params.proc_stddev_vx_c * dt * dt;
        Q[(StateIndex::Wz as usize, StateIndex::Wz as usize)] = 
            self.params.proc_stddev_wz_c * self.params.proc_stddev_wz_c * dt * dt;
        Q[(StateIndex::Yaw as usize, StateIndex::Yaw as usize)] = 
            self.params.proc_stddev_yaw_c * self.params.proc_stddev_yaw_c * dt * dt;
        
        // No process noise for position and yaw bias
        Q[(StateIndex::X as usize, StateIndex::X as usize)] = 0.0;
        Q[(StateIndex::Y as usize, StateIndex::Y as usize)] = 0.0;
        Q[(StateIndex::YawBias as usize, StateIndex::YawBias as usize)] = 0.0;
        
        Q
    }

    /// Predict step of EKF (uses predict_next_state, create_state_transition_matrix, and process_noise_covariance)
    pub fn predict(&mut self, dt: f64) {
        // 1. Predict next state using nonlinear motion model
        self.state = self.predict_next_state(dt);

        // 2. Create state transition (Jacobian) matrix
        let F = self.create_state_transition_matrix(dt);

        // 3. Calculate process noise covariance
        let Q = self.process_noise_covariance(dt);

        // 4. Predict covariance: P = F * P * F^T + Q
        self.covariance = F * self.covariance * F.transpose() + Q;

        // 5. Update accumulated delay times
        self.accumulate_delay_time(dt);
    }

    /// Predict with delay support (Autoware compatible)
    /// This version maintains the delay history for measurement updates
    pub fn predict_with_delay(&mut self, dt: f64) {
        self.predict(dt);
    }

    /// Predict-only step (for MRM mode when measurement updates are not available)
    /// Only performs prediction without any measurement updates
    pub fn predict_only(&mut self, dt: f64) {
        self.predict(dt);
    }

    /// Get current pose for tf publishing
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

    /// Get current twist
    pub fn get_current_twist(&self) -> Twist {
        let vx = self.state[StateIndex::Vx as usize];
        let wz = self.state[StateIndex::Wz as usize];

        Twist {
            linear: Vector3::new(vx, 0.0, 0.0),
            angular: Vector3::new(0.0, 0.0, wz),
        }
    }

    /// Get yaw bias
    pub fn get_yaw_bias(&self) -> f64 {
        self.state[StateIndex::YawBias as usize]
    }

    /// Get current pose with covariance for publishing
    pub fn get_current_pose_with_covariance(&self) -> PoseWithCovariance {
        // Get current pose
        let pose = self.get_current_pose(false);
        
        // Get covariance matrix
        let pose_covariance = self.get_current_pose_covariance();
        
        // Create and return PoseWithCovariance
        PoseWithCovariance {
            pose,
            covariance: pose_covariance,
        }
    }

    /// Get pose covariance (simplified 6x6 to 36-element array)
    pub fn get_current_pose_covariance(&self) -> [f64; 36] {
        let mut cov = [0.0; 36];
        
        // Copy 6x6 covariance matrix to 36-element array
        for i in 0..6 {
            for j in 0..6 {
                cov[i * 6 + j] = self.covariance[(i, j)];
            }
        }
        
        // Add z, roll, pitch variances
        cov[14] = self.z_filter.get_var();      // Z_Z
        cov[21] = self.roll_filter.get_var();   // ROLL_ROLL
        cov[28] = self.pitch_filter.get_var();  // PITCH_PITCH
        
        cov
    }

    /// Get twist covariance
    pub fn get_current_twist_covariance(&self) -> [f64; 36] {
        let mut cov = [0.0; 36];
        
        // Simplified: only vx and wz have significant covariance
        cov[0] = self.covariance[(StateIndex::Vx as usize, StateIndex::Vx as usize)];  // VX_VX
        cov[35] = self.covariance[(StateIndex::Wz as usize, StateIndex::Wz as usize)]; // WZ_WZ
        
        cov
    }

    /// Update velocity measurement (measurement update for Vx and Wz)
    /// This is NOT executed during MRM mode (dead reckoning only)
    pub fn update_velocity(&mut self, vx_measurement: f64, wz_measurement: f64) {
        // Skip measurement update during MRM mode
        if self.is_mrm_mode {
            return;
        }

        // Simple measurement update using Kalman gain
        // This assumes direct observation of velocity states
        
        // Measurement variance (assumed)
        let vx_obs_var = 1.0;
        let wz_obs_var = 0.1;
        
        // Update Vx
        let vx_var = self.covariance[(StateIndex::Vx as usize, StateIndex::Vx as usize)];
        let vx_gain = vx_var / (vx_var + vx_obs_var);
        self.state[StateIndex::Vx as usize] = 
            self.state[StateIndex::Vx as usize] + 
            vx_gain * (vx_measurement - self.state[StateIndex::Vx as usize]);
        self.covariance[(StateIndex::Vx as usize, StateIndex::Vx as usize)] = 
            (1.0 - vx_gain) * vx_var;
        
        // Update Wz
        let wz_var = self.covariance[(StateIndex::Wz as usize, StateIndex::Wz as usize)];
        let wz_gain = wz_var / (wz_var + wz_obs_var);
        self.state[StateIndex::Wz as usize] = 
            self.state[StateIndex::Wz as usize] + 
            wz_gain * (wz_measurement - self.state[StateIndex::Wz as usize]);
        self.covariance[(StateIndex::Wz as usize, StateIndex::Wz as usize)] = 
            (1.0 - wz_gain) * wz_var;
    }

    /// Set MRM (Minimal Risk Maneuver) mode
    /// When MRM mode is active, only prediction is performed (no measurement updates)
    pub fn set_mrm_mode(&mut self, is_mrm: bool) {
        self.is_mrm_mode = is_mrm;
    }

    /// Get current MRM mode status
    pub fn is_mrm(&self) -> bool {
        self.is_mrm_mode
    }

    /// Accumulate delay time
    pub fn accumulate_delay_time(&mut self, dt: f64) {
        let len = self.accumulated_delay_times.len();
        if len == 0 {
            return;
        }
        
        let last_time = self.accumulated_delay_times[len - 1];
        let new_time = last_time + dt;
        
        // Shift and add new time
        for i in 0..len - 1 {
            self.accumulated_delay_times[i] = self.accumulated_delay_times[i + 1];
        }
        self.accumulated_delay_times[len - 1] = new_time;
    }

    /// Find closest delay time index
    pub fn find_closest_delay_time_index(&self, target_value: f64) -> usize {
        let len = self.accumulated_delay_times.len();
        if len == 0 {
            return 0;
        }

        if target_value > self.accumulated_delay_times[len - 1] {
            return len;
        }

        // Simple linear search for closest value
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

    // Utility functions for quaternion and euler angle conversions
    fn quaternion_to_yaw(&self, q: Quaternion) -> f64 {
        atan2(2.0 * (q.w * q.z + q.x * q.y), 1.0 - 2.0 * (q.y * q.y + q.z * q.z))
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

    fn quaternion_to_rpy(&self, q: Quaternion) -> (f64, f64, f64) {
        // Roll (x-axis rotation)
        let sinr_cosp = 2.0 * (q.w * q.x + q.y * q.z);
        let cosr_cosp = 1.0 - 2.0 * (q.x * q.x + q.y * q.y);
        let roll = atan2(sinr_cosp, cosr_cosp);

        // Pitch (y-axis rotation)
        let sinp = 2.0 * (q.w * q.y - q.z * q.x);
        let pitch = if sinp.abs() >= 1.0 {
            PI / 2.0 * sinp.signum()
        } else {
            asin(sinp)
        };

        // Yaw (z-axis rotation)
        let siny_cosp = 2.0 * (q.w * q.z + q.x * q.y);
        let cosy_cosp = 1.0 - 2.0 * (q.y * q.y + q.z * q.z);
        let yaw = atan2(siny_cosp, cosy_cosp);

        (roll, pitch, yaw)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ekf_initialization() {
        let params = EKFParameters::default();
        let mut ekf = EKFModule::new(params);
        
        let initial_pose = Pose {
            position: Point3D { x: 1.0, y: 2.0, z: 0.0 },
            orientation: Quaternion { x: 0.0, y: 0.0, z: 0.0, w: 1.0 },
        };
        
        ekf.initialize(initial_pose);
        
        let pose = ekf.get_current_pose(false);
        assert!((pose.position.x - 1.0).abs() < 1e-6);
        assert!((pose.position.y - 2.0).abs() < 1e-6);
    }

    #[test]
    fn test_quaternion_conversions() {
        let params = EKFParameters::default();
        let ekf = EKFModule::new(params);
        
        let roll = 0.1;
        let pitch = 0.2;
        let yaw = 0.3;
        
        let q = ekf.rpy_to_quaternion(roll, pitch, yaw);
        let (r, p, y) = ekf.quaternion_to_rpy(q);
        
        assert!((roll - r).abs() < 1e-6);
        assert!((pitch - p).abs() < 1e-6);
        assert!((yaw - y).abs() < 1e-6);
    }

    #[test]
    fn test_pose_with_covariance_generation() {
        let params = EKFParameters::default();
        let mut ekf = EKFModule::new(params);
        
        let initial_pose = Pose {
            position: Point3D { x: 1.0, y: 2.0, z: 0.0 },
            orientation: Quaternion { x: 0.0, y: 0.0, z: 0.0, w: 1.0 },
        };
        
        ekf.initialize(initial_pose);
        
        let pose_with_cov = ekf.get_current_pose_with_covariance();
        
        // Check pose
        assert!((pose_with_cov.pose.position.x - 1.0).abs() < 1e-6);
        assert!((pose_with_cov.pose.position.y - 2.0).abs() < 1e-6);
        
        // Check covariance array
        assert_eq!(pose_with_cov.covariance.len(), 36);
    }
} 