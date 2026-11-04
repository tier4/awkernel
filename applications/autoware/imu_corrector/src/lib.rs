// Copyright 2020 Tier IV, Inc.
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
// Partially ported from the following versions of the original C++ code (See the TODO comment in ImuCorrectorConfig):
// universe/autoware_universe:
// type: git
// url: https://github.com/autowarefoundation/autoware_universe.git
// original file path: sensing/autoware_imu_corrector/src/imu_corrector_core.cpp
// test code: Created in-house for I/O verification
// version: 0.51.0

#![no_std]
extern crate alloc;

use alloc::{format, string::String};
use common_types::{Header, UnitQuaternion, Vector3};
use imu_driver::{ImuMsg, Quaternion};

#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Error {
    ZeroLengthQuaternion,
    NonFiniteQuaternion,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::ZeroLengthQuaternion => write!(f, "Zero length quaternion"),
            Error::NonFiniteQuaternion => write!(f, "Non-finite quaternion"),
        }
    }
}

impl core::error::Error for Error {}

#[derive(Clone, Debug)]
pub struct Transform {
    translation: Vector3<f64>,
    rotation: UnitQuaternion<f64>,
}

impl Transform {
    /// Creates a new `Transform` with the given translation and rotation.
    #[inline]
    pub const fn new(translation: Vector3<f64>, rotation: UnitQuaternion<f64>) -> Self {
        Self {
            translation,
            rotation,
        }
    }

    /// Tries to create a new `Transform` with the given translation and rotation.
    /// Returns an error if the rotation quaternion is zero-length or contains non-finite values.
    #[inline]
    pub fn try_new(translation: Vector3<f64>, rotation: Quaternion<f64>) -> Result<Self, Error> {
        if rotation.coords.iter().any(|value| !value.is_finite()) {
            Err(Error::NonFiniteQuaternion)
        } else if rotation.norm_squared() == 0.0 {
            Err(Error::ZeroLengthQuaternion)
        } else {
            Ok(Self::new(
                translation,
                UnitQuaternion::from_quaternion(rotation),
            ))
        }
    }

    /// Returns the identity transform (no translation, no rotation).
    #[inline]
    pub fn identity() -> Self {
        Self::new(Vector3::new(0.0, 0.0, 0.0), UnitQuaternion::identity())
    }

    /// Applies the transform to the given vector.
    #[inline]
    pub fn apply_to_vector(&self, vec: Vector3<f64>) -> Vector3<f64> {
        self.rotation * vec + self.translation
    }
}

pub trait TransformListener {
    fn get_latest_transform(&self, from_frame: &str, to_frame: &str) -> Option<Transform>;
    fn get_transform_at_time(
        &self,
        from_frame: &str,
        to_frame: &str,
        timestamp: u64,
    ) -> Option<Transform>;
}

pub struct MockTransformListener {
    transforms: alloc::collections::BTreeMap<String, Transform>,
}

impl MockTransformListener {
    pub fn new() -> Self {
        Self {
            transforms: alloc::collections::BTreeMap::new(),
        }
    }

    pub fn add_transform(&mut self, from_frame: &str, to_frame: &str, transform: Transform) {
        let key = format!("{}_to_{}", from_frame, to_frame);
        self.transforms.insert(key, transform);
    }
}

impl Default for MockTransformListener {
    fn default() -> Self {
        Self::new()
    }
}

impl TransformListener for MockTransformListener {
    fn get_latest_transform(&self, from_frame: &str, to_frame: &str) -> Option<Transform> {
        let key = format!("{}_to_{}", from_frame, to_frame);
        self.transforms.get(&key).cloned()
    }

    fn get_transform_at_time(
        &self,
        from_frame: &str,
        to_frame: &str,
        _timestamp: u64,
    ) -> Option<Transform> {
        self.get_latest_transform(from_frame, to_frame)
    }
}

#[derive(Clone, Debug)]
pub struct ImuWithCovariance {
    pub header: Header,
    pub angular_velocity: Vector3<f64>,
    pub angular_velocity_covariance: [f64; 9],
    pub linear_acceleration: Vector3<f64>,
    pub linear_acceleration_covariance: [f64; 9],
}

impl ImuWithCovariance {
    pub fn from_imu_msg(imu_msg: &ImuMsg) -> Self {
        Self {
            header: imu_msg.header.clone(),
            angular_velocity: imu_msg.angular_velocity,
            angular_velocity_covariance: [0.0; 9],
            linear_acceleration: imu_msg.linear_acceleration,
            linear_acceleration_covariance: [0.0; 9],
        }
    }

    pub fn to_imu_msg(&self) -> ImuMsg {
        ImuMsg {
            header: self.header.clone(),
            angular_velocity: self.angular_velocity,
            linear_acceleration: self.linear_acceleration,
        }
    }
}

// TODO: The `gyro_bias` and `gyro_scale` functions have not been implemented.
// Since this application is currently running on the MRM redundant system and for evaluation purposes,
// the absence of these functions does not cause any apparent issues at this time.
// However, since their behavior may change when processing data from
// “long-duration operations” or “high-precision real-world driving,” they will need to be added in the future.
pub struct ImuCorrectorConfig {
    pub angular_velocity_offset_x: f64,
    pub angular_velocity_offset_y: f64,
    pub angular_velocity_offset_z: f64,
    pub angular_velocity_stddev_xx: f64,
    pub angular_velocity_stddev_yy: f64,
    pub angular_velocity_stddev_zz: f64,
    pub acceleration_stddev: f64,
    pub output_frame: &'static str,
}

impl Default for ImuCorrectorConfig {
    fn default() -> Self {
        Self {
            angular_velocity_offset_x: 0.0,
            angular_velocity_offset_y: 0.0,
            angular_velocity_offset_z: 0.0,
            angular_velocity_stddev_xx: 0.03,
            angular_velocity_stddev_yy: 0.03,
            angular_velocity_stddev_zz: 0.03,
            acceleration_stddev: 10000.0,
            output_frame: "base_link",
        }
    }
}

pub struct ImuCorrector<T: TransformListener> {
    config: ImuCorrectorConfig,
    transform_listener: T,
}

impl ImuCorrector<MockTransformListener> {
    pub fn new() -> Self {
        Self {
            config: ImuCorrectorConfig::default(),
            transform_listener: MockTransformListener::new(),
        }
    }

    pub fn with_transform_listener(transform_listener: MockTransformListener) -> Self {
        Self {
            config: ImuCorrectorConfig::default(),
            transform_listener,
        }
    }
}

impl Default for ImuCorrector<MockTransformListener> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: TransformListener> ImuCorrector<T> {
    pub fn set_config(&mut self, config: ImuCorrectorConfig) {
        self.config = config;
    }

    fn transform_vector3(&self, vec: &Vector3<f64>, transform: &Transform) -> Vector3<f64> {
        transform.rotation * vec
    }

    fn transform_covariance_impl(cov: &[f64; 9]) -> [f64; 9] {
        let max_cov = cov[0].max(cov[4]).max(cov[8]);
        let mut cov_transformed = [0.0; 9];
        cov_transformed[0] = max_cov;
        cov_transformed[4] = max_cov;
        cov_transformed[8] = max_cov;

        cov_transformed
    }

    // NOTE: Unlike the original C++ implementation which returns early (without publishing)
    // when TF lookup fails, this implementation cannot do the same due to Awkernel DAG's
    // type constraints: all reactors must return their OutputTuple, and omitting output
    // would cause downstream reactors (e.g. gyro_odometer) to block indefinitely.
    //
    // Currently, the process continues even if `None` is passed, and the value does not
    // change after the transform. However, This was not caught during evaluation
    // because the TF used in testing had an identity rotation (translation only, no effect on vector values).
    // However, the actual vehicle TF would produce incorrect results if skipped.
    // TODO: To be implemented in a subsequent PR:
    // Fix by hardcoding a fixed tf value to prevent None from being passed by the caller.
    //
    // If dynamic TF support is added in the future, the recommended fallback is to
    // return an empty/zeroed ImuWithCovariance (analogous to `create_empty_twist` in
    // gyro_odometer) rather than uncorrected data, to avoid silently publishing
    // imu_link-frame data labelled as base_link.
    pub fn correct_imu_with_covariance(
        &self,
        imu_msg: &ImuMsg,
        transform: Option<&Transform>,
    ) -> ImuWithCovariance {
        let mut corrected_imu = ImuWithCovariance::from_imu_msg(imu_msg);
        corrected_imu.angular_velocity.x -= self.config.angular_velocity_offset_x;
        corrected_imu.angular_velocity.y -= self.config.angular_velocity_offset_y;
        corrected_imu.angular_velocity.z -= self.config.angular_velocity_offset_z;
        corrected_imu.angular_velocity_covariance[0] =
            self.config.angular_velocity_stddev_xx * self.config.angular_velocity_stddev_xx;
        corrected_imu.angular_velocity_covariance[4] =
            self.config.angular_velocity_stddev_yy * self.config.angular_velocity_stddev_yy;
        corrected_imu.angular_velocity_covariance[8] =
            self.config.angular_velocity_stddev_zz * self.config.angular_velocity_stddev_zz;
        let accel_var = self.config.acceleration_stddev * self.config.acceleration_stddev;
        corrected_imu.linear_acceleration_covariance[0] = accel_var;
        corrected_imu.linear_acceleration_covariance[4] = accel_var;
        corrected_imu.linear_acceleration_covariance[8] = accel_var;

        if let Some(tf) = transform {
            corrected_imu.linear_acceleration =
                self.transform_vector3(&corrected_imu.linear_acceleration, tf);
            corrected_imu.linear_acceleration_covariance =
                Self::transform_covariance_impl(&corrected_imu.linear_acceleration_covariance);
            corrected_imu.angular_velocity =
                self.transform_vector3(&corrected_imu.angular_velocity, tf);
            corrected_imu.angular_velocity_covariance =
                Self::transform_covariance_impl(&corrected_imu.angular_velocity_covariance);
            corrected_imu.header.frame_id = self.config.output_frame;
        }

        corrected_imu
    }

    pub fn correct_imu(&self, imu_msg: &ImuMsg, transform: Option<&Transform>) -> ImuMsg {
        let corrected_with_cov = self.correct_imu_with_covariance(imu_msg, transform);
        corrected_with_cov.to_imu_msg()
    }

    pub fn correct_imu_with_dynamic_tf(&self, imu_msg: &ImuMsg) -> Option<ImuMsg> {
        let transform = self
            .transform_listener
            .get_latest_transform(&imu_msg.header.frame_id, self.config.output_frame)?;

        let corrected_with_cov = self.correct_imu_with_covariance(imu_msg, Some(&transform));
        Some(corrected_with_cov.to_imu_msg())
    }

    pub fn correct_imu_with_dynamic_tf_covariance(
        &self,
        imu_msg: &ImuMsg,
    ) -> Option<ImuWithCovariance> {
        let transform = self
            .transform_listener
            .get_latest_transform(&imu_msg.header.frame_id, self.config.output_frame)?;

        Some(self.correct_imu_with_covariance(imu_msg, Some(&transform)))
    }

    pub fn correct_imu_simple(&self, imu_msg: &ImuMsg) -> ImuMsg {
        let mut corrected_msg = imu_msg.clone();

        corrected_msg.angular_velocity.x -= self.config.angular_velocity_offset_x;
        corrected_msg.angular_velocity.y -= self.config.angular_velocity_offset_y;
        corrected_msg.angular_velocity.z -= self.config.angular_velocity_offset_z;

        corrected_msg.header.frame_id = self.config.output_frame;

        corrected_msg
    }

    pub fn get_covariance_config(&self) -> (f64, f64, f64, f64) {
        (
            self.config.angular_velocity_stddev_xx,
            self.config.angular_velocity_stddev_yy,
            self.config.angular_velocity_stddev_zz,
            self.config.acceleration_stddev,
        )
    }
}

pub fn transform_covariance(cov: &[f64; 9]) -> [f64; 9] {
    ImuCorrector::<MockTransformListener>::transform_covariance_impl(cov)
}

#[cfg(test)]
mod tests {
    use super::*;
    use common_types::Quaternion;

    fn assert_almost_eq(actual: f64, expected: f64) {
        assert!((actual - expected).abs() < 1e-10);
    }

    fn sample_imu_msg() -> ImuMsg {
        ImuMsg {
            header: Header {
                frame_id: "imu_link",
                timestamp: 0,
            },
            angular_velocity: Vector3::new(0.1, 0.2, 0.3),
            linear_acceleration: Vector3::new(9.8, 0.0, 0.0),
        }
    }

    #[test]
    fn try_new_rejects_zero_length_quaternion() {
        let result = Transform::try_new(Vector3::zeros(), Quaternion::new(0.0, 0.0, 0.0, 0.0));

        assert!(matches!(result, Err(Error::ZeroLengthQuaternion)));
    }

    #[test]
    fn try_new_rejects_non_finite_quaternion_components() {
        for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            for rotation in [
                Quaternion::new(value, 0.0, 0.0, 0.0),
                Quaternion::new(1.0, value, 0.0, 0.0),
                Quaternion::new(1.0, 0.0, value, 0.0),
                Quaternion::new(1.0, 0.0, 0.0, value),
            ] {
                let result = Transform::try_new(Vector3::zeros(), rotation);

                assert!(
                    matches!(result, Err(Error::NonFiniteQuaternion)),
                    "expected NonFiniteQuaternion for {rotation:?}"
                );
            }
        }
    }

    #[test]
    fn try_new_rejects_quaternion_with_underflowing_squared_norm() {
        let rotation = Quaternion::new(f64::MIN_POSITIVE, 0.0, 0.0, 0.0);
        let result = Transform::try_new(Vector3::zeros(), rotation);

        assert!(matches!(result, Err(Error::ZeroLengthQuaternion)));
    }

    #[test]
    fn try_new_normalizes_valid_quaternion_and_preserves_translation() {
        let translation = Vector3::new(1.0, 2.0, 3.0);
        let rotation = Quaternion::new(2.0, 0.0, 0.0, 2.0);
        let transform = Transform::try_new(translation, rotation).unwrap();

        assert_eq!(transform.translation, translation);
        assert_almost_eq(transform.rotation.norm(), 1.0);

        let transformed = transform.apply_to_vector(Vector3::new(1.0, 0.0, 0.0));
        assert_almost_eq(transformed.x, 1.0);
        assert_almost_eq(transformed.y, 3.0);
        assert_almost_eq(transformed.z, 3.0);
    }

    #[test]
    fn identity_transform_preserves_vector() {
        let vector = Vector3::new(1.0, -2.0, 3.0);
        let transformed = Transform::identity().apply_to_vector(vector);

        assert_almost_eq(transformed.x, vector.x);
        assert_almost_eq(transformed.y, vector.y);
        assert_almost_eq(transformed.z, vector.z);
    }

    #[test]
    fn transform_rotates_then_translates_vector() {
        let half_sqrt_two = core::f64::consts::FRAC_1_SQRT_2;
        let translation = Vector3::new(1.0, 2.0, 3.0);
        let rotation = Quaternion::new(half_sqrt_two, 0.0, 0.0, half_sqrt_two);

        let transform = Transform::try_new(translation, rotation);
        assert!(transform.is_ok());
        let transform = transform.unwrap();

        let transformed = transform.apply_to_vector(Vector3::new(1.0, 0.0, 0.0));

        assert_almost_eq(transformed.x, 1.0);
        assert_almost_eq(transformed.y, 3.0);
        assert_almost_eq(transformed.z, 3.0);
    }

    #[test]
    fn static_bias_correction_updates_angular_velocity() {
        let mut config = ImuCorrectorConfig::default();
        config.angular_velocity_offset_x = 0.05;
        config.angular_velocity_offset_y = 0.1;
        config.angular_velocity_offset_z = 0.15;

        let mut corrector = ImuCorrector::new();
        corrector.set_config(config);

        let imu_msg = sample_imu_msg();
        let corrected = corrector.correct_imu(&imu_msg, None);

        assert_eq!(corrected.angular_velocity.x, 0.05);
        assert_eq!(corrected.angular_velocity.y, 0.1);
        assert_eq!(corrected.angular_velocity.z, 0.15);
        assert_eq!(corrected.header.frame_id, "imu_link");
    }

    #[test]
    fn simple_path_sets_output_frame() {
        let corrector = ImuCorrector::new();
        let imu_msg = sample_imu_msg();

        let corrected_msg = corrector.correct_imu_simple(&imu_msg);

        assert_eq!(corrected_msg.header.frame_id, "base_link");
        assert_eq!(corrected_msg.angular_velocity.x, 0.1);
        assert_eq!(corrected_msg.angular_velocity.y, 0.2);
        assert_eq!(corrected_msg.angular_velocity.z, 0.3);
    }

    #[test]
    fn covariance_defaults_are_set_from_config() {
        let corrector = ImuCorrector::new();
        let imu_msg = sample_imu_msg();

        let corrected_with_cov = corrector.correct_imu_with_covariance(&imu_msg, None);
        let expected_angular_var = 0.03 * 0.03;
        assert_eq!(
            corrected_with_cov.angular_velocity_covariance[0],
            expected_angular_var
        );
        assert_eq!(
            corrected_with_cov.angular_velocity_covariance[4],
            expected_angular_var
        );
        assert_eq!(
            corrected_with_cov.angular_velocity_covariance[8],
            expected_angular_var
        );
        let expected_accel_var = 10000.0 * 10000.0;
        assert_eq!(
            corrected_with_cov.linear_acceleration_covariance[0],
            expected_accel_var
        );
        assert_eq!(
            corrected_with_cov.linear_acceleration_covariance[4],
            expected_accel_var
        );
        assert_eq!(
            corrected_with_cov.linear_acceleration_covariance[8],
            expected_accel_var
        );
    }

    #[test]
    fn covariance_transform_uses_max_diagonal() {
        let input_cov = [1.0, 0.5, 0.3, 0.5, 2.0, 0.4, 0.3, 0.4, 3.0];
        let transformed_cov = transform_covariance(&input_cov);
        assert_eq!(transformed_cov[0], 3.0);
        assert_eq!(transformed_cov[4], 3.0);
        assert_eq!(transformed_cov[8], 3.0);
        assert_eq!(transformed_cov[1], 0.0);
        assert_eq!(transformed_cov[2], 0.0);
        assert_eq!(transformed_cov[3], 0.0);
        assert_eq!(transformed_cov[5], 0.0);
        assert_eq!(transformed_cov[6], 0.0);
        assert_eq!(transformed_cov[7], 0.0);
    }

    #[test]
    fn transform_applies_to_vectors_and_sets_output_frame() {
        let corrector = ImuCorrector::new();
        let imu_msg = sample_imu_msg();

        let half_sqrt_two = core::f64::consts::FRAC_1_SQRT_2;
        let translation = Vector3::new(1.0, 2.0, 3.0);
        let rotation = Quaternion::new(half_sqrt_two, 0.0, 0.0, half_sqrt_two);

        let transform = Transform::try_new(translation, rotation);
        assert!(transform.is_ok());
        let transform = transform.unwrap();

        let corrected_with_cov = corrector.correct_imu_with_covariance(&imu_msg, Some(&transform));
        assert_eq!(corrected_with_cov.header.frame_id, "base_link");
        assert_almost_eq(corrected_with_cov.linear_acceleration.x, 0.0);
        assert_almost_eq(corrected_with_cov.linear_acceleration.y, 9.8);
        assert_almost_eq(corrected_with_cov.linear_acceleration.z, 0.0);
        assert_almost_eq(corrected_with_cov.angular_velocity.x, -0.2);
        assert_almost_eq(corrected_with_cov.angular_velocity.y, 0.1);
        assert_almost_eq(corrected_with_cov.angular_velocity.z, 0.3);
    }

    #[test]
    fn dynamic_tf_path_applies_transform() {
        let mut transform_listener = MockTransformListener::new();
        let transform = Transform {
            translation: Vector3::new(1.0, 0.0, 0.0),
            rotation: UnitQuaternion::identity(),
        };
        transform_listener.add_transform("imu_link", "base_link", transform);

        let corrector = ImuCorrector::with_transform_listener(transform_listener);
        let imu_msg = sample_imu_msg();

        let corrected_msg = corrector.correct_imu_with_dynamic_tf(&imu_msg);
        assert!(corrected_msg.is_some());

        let corrected_msg = corrected_msg.unwrap();
        assert_eq!(corrected_msg.header.frame_id, "base_link");
        assert_eq!(corrected_msg.linear_acceleration.x, 9.8);
        assert_eq!(corrected_msg.linear_acceleration.y, 0.0);
        assert_eq!(corrected_msg.linear_acceleration.z, 0.0);
    }

    #[test]
    fn dynamic_tf_path_returns_none_when_transform_is_missing() {
        let transform_listener = MockTransformListener::new();
        let corrector = ImuCorrector::with_transform_listener(transform_listener);
        let imu_msg = sample_imu_msg();

        let corrected_msg = corrector.correct_imu_with_dynamic_tf(&imu_msg);
        assert!(corrected_msg.is_none());
    }
}
