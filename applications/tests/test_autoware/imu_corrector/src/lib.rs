#![no_std]
extern crate alloc;

use alloc::{format, string::String};
use imu_driver::{Header, ImuMsg, Quaternion, Vector3};
use nalgebra::{Quaternion as NQuaternion, UnitQuaternion, Vector3 as NVector3};

#[derive(Clone, Debug)]
pub struct Transform {
    pub translation: Vector3,
    pub rotation: Quaternion,
}

impl Transform {
    pub fn identity() -> Self {
        Self {
            translation: imu_driver::Vector3::new(5.22444, 0.07615, 2.72762), // use aip_x2_gen2_description.
            rotation: imu_driver::Quaternion {
                x: 1.0,
                y: 0.0,
                z: 0.0,
                w: 0.0,
            },
        }
    }

    fn to_nalgebra_vector3(&self, vec: &Vector3) -> NVector3<f64> {
        NVector3::new(vec.x, vec.y, vec.z)
    }

    fn to_imu_vector3(&self, vec: &NVector3<f64>) -> Vector3 {
        Vector3::new(vec.x, vec.y, vec.z)
    }

    fn to_nalgebra_quaternion(&self, quat: &Quaternion) -> UnitQuaternion<f64> {
        let n_quat = NQuaternion::new(quat.w, quat.x, quat.y, quat.z);
        UnitQuaternion::from_quaternion(n_quat)
    }

    pub fn apply_to_vector(&self, vec: Vector3) -> Vector3 {
        let nalgebra_vec = self.to_nalgebra_vector3(&vec);
        let nalgebra_quat = self.to_nalgebra_quaternion(&self.rotation);
        let nalgebra_trans = self.to_nalgebra_vector3(&self.translation);
        let rotated = nalgebra_quat * nalgebra_vec;
        let result = rotated + nalgebra_trans;
        self.to_imu_vector3(&result)
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
    pub orientation: Quaternion,
    pub angular_velocity: Vector3,
    pub angular_velocity_covariance: [f64; 9],
    pub linear_acceleration: Vector3,
    pub linear_acceleration_covariance: [f64; 9],
}

impl ImuWithCovariance {
    pub fn from_imu_msg(imu_msg: &ImuMsg) -> Self {
        Self {
            header: imu_msg.header.clone(),
            orientation: imu_msg.orientation.clone(),
            angular_velocity: imu_msg.angular_velocity.clone(),
            angular_velocity_covariance: [0.0; 9],
            linear_acceleration: imu_msg.linear_acceleration.clone(),
            linear_acceleration_covariance: [0.0; 9],
        }
    }

    pub fn to_imu_msg(&self) -> ImuMsg {
        ImuMsg {
            header: self.header.clone(),
            orientation: self.orientation.clone(),
            angular_velocity: self.angular_velocity.clone(),
            linear_acceleration: self.linear_acceleration.clone(),
        }
    }
}

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

impl<T: TransformListener> ImuCorrector<T> {
    pub fn set_config(&mut self, config: ImuCorrectorConfig) {
        self.config = config;
    }

    fn to_nalgebra_vector3(&self, vec: &Vector3) -> NVector3<f64> {
        NVector3::new(vec.x, vec.y, vec.z)
    }

    fn to_imu_vector3(&self, vec: &NVector3<f64>) -> Vector3 {
        Vector3::new(vec.x, vec.y, vec.z)
    }

    fn to_nalgebra_quaternion(&self, quat: &Quaternion) -> UnitQuaternion<f64> {
        let n_quat = NQuaternion::new(quat.w, quat.x, quat.y, quat.z);
        UnitQuaternion::from_quaternion(n_quat)
    }

    fn transform_vector3(&self, vec: &Vector3, transform: &Transform) -> Vector3 {
        let nalgebra_vec = self.to_nalgebra_vector3(vec);
        let nalgebra_quat = self.to_nalgebra_quaternion(&transform.rotation);
        let nalgebra_trans = self.to_nalgebra_vector3(&transform.translation);
        let rotated = nalgebra_quat * nalgebra_vec;
        let result = rotated + nalgebra_trans;
        self.to_imu_vector3(&result)
    }

    fn transform_covariance(&self, cov: &[f64; 9]) -> [f64; 9] {
        let max_cov = cov[0].max(cov[4]).max(cov[8]);
        let mut cov_transformed = [0.0; 9];
        cov_transformed[0] = max_cov;
        cov_transformed[4] = max_cov;
        cov_transformed[8] = max_cov;

        cov_transformed
    }

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
                self.transform_covariance(&corrected_imu.linear_acceleration_covariance);
            corrected_imu.angular_velocity =
                self.transform_vector3(&corrected_imu.angular_velocity, tf);
            corrected_imu.angular_velocity_covariance =
                self.transform_covariance(&corrected_imu.angular_velocity_covariance);
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
    let max_cov = cov[0].max(cov[4]).max(cov[8]);
    let mut cov_transformed = [0.0; 9];
    cov_transformed[0] = max_cov;
    cov_transformed[4] = max_cov;
    cov_transformed[8] = max_cov;
    cov_transformed
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_imu_corrector() {
        let corrector = ImuCorrector::new();
        let imu_msg = ImuMsg {
            header: Header {
                frame_id: "imu_link",
                timestamp: 0,
            },
            orientation: Quaternion {
                x: 0.0,
                y: 0.0,
                z: 0.0,
                w: 1.0,
            },
            angular_velocity: Vector3::new(0.1, 0.2, 0.3),
            linear_acceleration: Vector3::new(9.8, 0.0, 0.0),
        };

        let corrected_msg = corrector.correct_imu_simple(&imu_msg);
        assert_eq!(corrected_msg.header.frame_id, "base_link");
        assert_eq!(corrected_msg.angular_velocity.x, 0.1);
        assert_eq!(corrected_msg.angular_velocity.y, 0.2);
        assert_eq!(corrected_msg.angular_velocity.z, 0.3);
    }

    #[test]
    fn test_imu_corrector_with_offset() {
        let mut config = ImuCorrectorConfig::default();
        config.angular_velocity_offset_x = 0.05;
        config.angular_velocity_offset_y = 0.1;
        config.angular_velocity_offset_z = 0.15;

        let mut corrector = ImuCorrector::new();
        corrector.set_config(config);

        let imu_msg = ImuMsg {
            header: Header {
                frame_id: "imu_link",
                timestamp: 0,
            },
            orientation: Quaternion {
                x: 0.0,
                y: 0.0,
                z: 0.0,
                w: 1.0,
            },
            angular_velocity: Vector3::new(0.1, 0.2, 0.3),
            linear_acceleration: Vector3::new(9.8, 0.0, 0.0),
        };

        let corrected_msg = corrector.correct_imu_simple(&imu_msg);

        assert_eq!(corrected_msg.angular_velocity.x, 0.1 - 0.05);
        assert_eq!(corrected_msg.angular_velocity.y, 0.2 - 0.1);
        assert_eq!(corrected_msg.angular_velocity.z, 0.3 - 0.15);
    }

    #[test]
    fn test_imu_corrector_with_covariance() {
        let corrector = ImuCorrector::new();
        let imu_msg = ImuMsg {
            header: Header {
                frame_id: "imu_link",
                timestamp: 0,
            },
            orientation: Quaternion {
                x: 0.0,
                y: 0.0,
                z: 0.0,
                w: 1.0,
            },
            angular_velocity: Vector3::new(0.1, 0.2, 0.3),
            linear_acceleration: Vector3::new(9.8, 0.0, 0.0),
        };

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
    fn test_transform_covariance() {
        let corrector = ImuCorrector::new();
        let input_cov = [1.0, 0.5, 0.3, 0.5, 2.0, 0.4, 0.3, 0.4, 3.0];
        let transformed_cov = corrector.transform_covariance(&input_cov);

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
    fn test_public_transform_covariance() {
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
    fn test_imu_corrector_with_transform() {
        let corrector = ImuCorrector::new();
        let imu_msg = ImuMsg {
            header: Header {
                frame_id: "imu_link",
                timestamp: 0,
            },
            orientation: Quaternion {
                x: 0.0,
                y: 0.0,
                z: 0.0,
                w: 1.0,
            },
            angular_velocity: Vector3::new(0.1, 0.2, 0.3),
            linear_acceleration: Vector3::new(9.8, 0.0, 0.0),
        };

        let transform = Transform {
            translation: Vector3::new(0.0, 0.0, 0.0),
            rotation: Quaternion {
                x: 0.0,
                y: 0.0,
                z: 0.0,
                w: 1.0,
            },
        };

        let corrected_with_cov = corrector.correct_imu_with_covariance(&imu_msg, Some(&transform));
        assert_eq!(corrected_with_cov.header.frame_id, "base_link");
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
    }

    #[test]
    fn test_imu_corrector_with_dynamic_tf() {
        let mut transform_listener = MockTransformListener::new();
        let transform = Transform {
            translation: Vector3::new(1.0, 0.0, 0.0),
            rotation: Quaternion {
                x: 0.0,
                y: 0.0,
                z: 0.0,
                w: 1.0,
            },
        };
        transform_listener.add_transform("imu_link", "base_link", transform);

        let corrector = ImuCorrector::with_transform_listener(transform_listener);
        let imu_msg = ImuMsg {
            header: Header {
                frame_id: "imu_link",
                timestamp: 0,
            },
            orientation: Quaternion {
                x: 0.0,
                y: 0.0,
                z: 0.0,
                w: 1.0,
            },
            angular_velocity: Vector3::new(0.1, 0.2, 0.3),
            linear_acceleration: Vector3::new(9.8, 0.0, 0.0),
        };

        let corrected_msg = corrector.correct_imu_with_dynamic_tf(&imu_msg);
        assert!(corrected_msg.is_some());

        let corrected_msg = corrected_msg.unwrap();
        assert_eq!(corrected_msg.header.frame_id, "base_link");
        assert_eq!(corrected_msg.linear_acceleration.x, 9.8);
    }

    #[test]
    fn test_imu_corrector_with_dynamic_tf_no_transform() {
        let transform_listener = MockTransformListener::new();
        let corrector = ImuCorrector::with_transform_listener(transform_listener);
        let imu_msg = ImuMsg {
            header: Header {
                frame_id: "imu_link",
                timestamp: 0,
            },
            orientation: Quaternion {
                x: 0.0,
                y: 0.0,
                z: 0.0,
                w: 1.0,
            },
            angular_velocity: Vector3::new(0.1, 0.2, 0.3),
            linear_acceleration: Vector3::new(9.8, 0.0, 0.0),
        };

        let corrected_msg = corrector.correct_imu_with_dynamic_tf(&imu_msg);
        assert!(corrected_msg.is_none());
    }
}
