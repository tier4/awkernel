#![no_std]
extern crate alloc;

use nalgebra::{Matrix3, UnitQuaternion, Vector3 as NVector3, Quaternion as NQuaternion};
use imu_driver::{ImuMsg, Vector3, Quaternion, Header};
use alloc::{format, string::String};

// Transform structure (simplified TF representation)
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

    /// Convert imu_driver Vector3 to nalgebra Vector3
    fn to_nalgebra_vector3(&self, vec: &Vector3) -> NVector3<f64> {
        NVector3::new(vec.x, vec.y, vec.z)
    }

    /// Convert nalgebra Vector3 to imu_driver Vector3
    fn to_imu_vector3(&self, vec: &NVector3<f64>) -> Vector3 {
        Vector3::new(vec.x, vec.y, vec.z)
    }

    /// Convert imu_driver Quaternion to nalgebra UnitQuaternion
    fn to_nalgebra_quaternion(&self, quat: &Quaternion) -> UnitQuaternion<f64> {
        // Create nalgebra Quaternion first, then normalize to UnitQuaternion
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

// Dynamic TF listener interface (simplified version)
pub trait TransformListener {
    fn get_latest_transform(&self, from_frame: &str, to_frame: &str) -> Option<Transform>;
    fn get_transform_at_time(&self, from_frame: &str, to_frame: &str, timestamp: u64) -> Option<Transform>;
}

// Mock TF listener for testing (can be replaced with actual ROS2 TF implementation)
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

    fn get_transform_at_time(&self, from_frame: &str, to_frame: &str, _timestamp: u64) -> Option<Transform> {
        // For mock implementation, ignore timestamp and return latest
        self.get_latest_transform(from_frame, to_frame)
    }
}

// Enhanced IMU structure with covariance information
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

// Configuration structure
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
    //sensing/autoware_imu_corrector/config/imu_corrector.param.yaml
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

// IMU corrector implementation
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

    /// Convert imu_driver Vector3 to nalgebra Vector3
    fn to_nalgebra_vector3(&self, vec: &Vector3) -> NVector3<f64> {
        NVector3::new(vec.x, vec.y, vec.z)
    }

    /// Convert nalgebra Vector3 to imu_driver Vector3
    fn to_imu_vector3(&self, vec: &NVector3<f64>) -> Vector3 {
        Vector3::new(vec.x, vec.y, vec.z)
    }

    /// Convert imu_driver Quaternion to nalgebra UnitQuaternion
    fn to_nalgebra_quaternion(&self, quat: &Quaternion) -> UnitQuaternion<f64> {
        // Create nalgebra Quaternion first, then normalize to UnitQuaternion
        let n_quat = NQuaternion::new(quat.w, quat.x, quat.y, quat.z);
        UnitQuaternion::from_quaternion(n_quat)
    }

    /// Transform vector3 using transform (simplified version)
    fn transform_vector3(&self, vec: &Vector3, transform: &Transform) -> Vector3 {
        // Convert to nalgebra types for transformation
        let nalgebra_vec = self.to_nalgebra_vector3(vec);
        let nalgebra_quat = self.to_nalgebra_quaternion(&transform.rotation);
        let nalgebra_trans = self.to_nalgebra_vector3(&transform.translation);
        
        // Apply rotation and translation
        let rotated = nalgebra_quat * nalgebra_vec;
        let result = rotated + nalgebra_trans;
        
        // Convert back to imu_driver Vector3
        self.to_imu_vector3(&result)
    }

    /// Transform covariance matrix (matches C++ transform_covariance function)
    /// Takes the maximum covariance value and applies it to diagonal elements
    fn transform_covariance(&self, cov: &[f64; 9]) -> [f64; 9] {
        // Find maximum covariance value from diagonal elements (xx, yy, zz)
        let max_cov = cov[0].max(cov[4]).max(cov[8]); // X_X, Y_Y, Z_Z indices
        
        // Create new covariance matrix with max_cov on diagonal, zeros elsewhere
        let mut cov_transformed = [0.0; 9];
        cov_transformed[0] = max_cov; // X_X
        cov_transformed[4] = max_cov; // Y_Y
        cov_transformed[8] = max_cov; // Z_Z
        // Other elements remain 0.0
        
        cov_transformed
    }

    /// Create default covariance matrix as array
    fn create_default_covariance_array(&self) -> [f64; 9] {
        [0.0; 9]
    }

    /// Convert Matrix3 to array format for compatibility
    fn matrix3_to_array(&self, matrix: &Matrix3<f64>) -> [f64; 9] {
        [
            matrix[(0, 0)], matrix[(0, 1)], matrix[(0, 2)],
            matrix[(1, 0)], matrix[(1, 1)], matrix[(1, 2)],
            matrix[(2, 0)], matrix[(2, 1)], matrix[(2, 2)],
        ]
    }

    /// Correct IMU data with covariance (enhanced version for gyro_odometer)
    /// This function matches the C++ callback_imu function more faithfully
    pub fn correct_imu_with_covariance(&self, imu_msg: &ImuMsg, transform: Option<&Transform>) -> ImuWithCovariance {
        // Start with a copy of the input IMU message (matches C++ line 82)
        let mut corrected_imu = ImuWithCovariance::from_imu_msg(imu_msg);

        // Apply angular velocity offset correction (matches C++ lines 85-87)
        corrected_imu.angular_velocity.x -= self.config.angular_velocity_offset_x;
        corrected_imu.angular_velocity.y -= self.config.angular_velocity_offset_y;
        corrected_imu.angular_velocity.z -= self.config.angular_velocity_offset_z;

        // Calculate angular velocity covariance (matches C++ lines 89-93)
        // Convert to array format: [xx, xy, xz, yx, yy, yz, zx, zy, zz]
        corrected_imu.angular_velocity_covariance[0] = 
            self.config.angular_velocity_stddev_xx * self.config.angular_velocity_stddev_xx; // xx
        corrected_imu.angular_velocity_covariance[4] = 
            self.config.angular_velocity_stddev_yy * self.config.angular_velocity_stddev_yy; // yy
        corrected_imu.angular_velocity_covariance[8] = 
            self.config.angular_velocity_stddev_zz * self.config.angular_velocity_stddev_zz; // zz

        // Calculate acceleration covariance (matches C++ lines 98-103)
        let accel_var = self.config.acceleration_stddev * self.config.acceleration_stddev;
        corrected_imu.linear_acceleration_covariance[0] = accel_var; // xx
        corrected_imu.linear_acceleration_covariance[4] = accel_var; // yy
        corrected_imu.linear_acceleration_covariance[8] = accel_var; // zz

        // Apply TF transformation if provided (matches C++ lines 105-125)
        if let Some(tf) = transform {
            // Transform linear acceleration (matches C++ line 115)
            corrected_imu.linear_acceleration = self.transform_vector3(&corrected_imu.linear_acceleration, tf);
            // Transform linear acceleration covariance (matches C++ line 116)
            corrected_imu.linear_acceleration_covariance = 
                self.transform_covariance(&corrected_imu.linear_acceleration_covariance);
            
            // Transform angular velocity (matches C++ line 118)
            corrected_imu.angular_velocity = self.transform_vector3(&corrected_imu.angular_velocity, tf);
            // Transform angular velocity covariance (matches C++ line 119)
            corrected_imu.angular_velocity_covariance = 
                self.transform_covariance(&corrected_imu.angular_velocity_covariance);
            
            // Update frame_id (matches C++ line 113)
            corrected_imu.header.frame_id = self.config.output_frame;
        }

        corrected_imu
    }

    /// Correct IMU data (matches C++ implementation more closely)
    pub fn correct_imu(&self, imu_msg: &ImuMsg, transform: Option<&Transform>) -> ImuMsg {
        let corrected_with_cov = self.correct_imu_with_covariance(imu_msg, transform);
        corrected_with_cov.to_imu_msg()
    }

    /// Correct IMU data with dynamic TF lookup (matches C++ callback_imu function)
    pub fn correct_imu_with_dynamic_tf(&self, imu_msg: &ImuMsg) -> Option<ImuMsg> {
        // Get latest transform dynamically (matches C++ lines 106-107)
        let transform = self.transform_listener.get_latest_transform(
            &imu_msg.header.frame_id, 
            self.config.output_frame
        )?;

        // Apply correction with the dynamic transform
        let corrected_with_cov = self.correct_imu_with_covariance(imu_msg, Some(&transform));
        Some(corrected_with_cov.to_imu_msg())
    }

    /// Correct IMU data with dynamic TF lookup and covariance
    pub fn correct_imu_with_dynamic_tf_covariance(&self, imu_msg: &ImuMsg) -> Option<ImuWithCovariance> {
        // Get latest transform dynamically (matches C++ lines 106-107)
        let transform = self.transform_listener.get_latest_transform(
            &imu_msg.header.frame_id, 
            self.config.output_frame
        )?;

        // Apply correction with the dynamic transform
        Some(self.correct_imu_with_covariance(imu_msg, Some(&transform)))
    }

    /// Correct IMU data without TF transformation (simplified version)
    pub fn correct_imu_simple(&self, imu_msg: &ImuMsg) -> ImuMsg {
        let mut corrected_msg = imu_msg.clone();

        // Apply angular velocity offset correction
        corrected_msg.angular_velocity.x -= self.config.angular_velocity_offset_x;
        corrected_msg.angular_velocity.y -= self.config.angular_velocity_offset_y;
        corrected_msg.angular_velocity.z -= self.config.angular_velocity_offset_z;

        // Update frame_id
        corrected_msg.header.frame_id = self.config.output_frame;
        
        corrected_msg
    }

    /// Get covariance configuration for external use
    pub fn get_covariance_config(&self) -> (f64, f64, f64, f64) {
        (
            self.config.angular_velocity_stddev_xx,
            self.config.angular_velocity_stddev_yy,
            self.config.angular_velocity_stddev_zz,
            self.config.acceleration_stddev,
        )
    }
}

/// Public transform_covariance function that can be called from other libraries
/// Transform covariance matrix (matches C++ transform_covariance function)
/// Takes the maximum covariance value and applies it to diagonal elements
pub fn transform_covariance(cov: &[f64; 9]) -> [f64; 9] {
    // Find maximum covariance value from diagonal elements (xx, yy, zz)
    let max_cov = cov[0].max(cov[4]).max(cov[8]); // X_X, Y_Y, Z_Z indices
    
    // Create new covariance matrix with max_cov on diagonal, zeros elsewhere
    let mut cov_transformed = [0.0; 9];
    cov_transformed[0] = max_cov; // X_X
    cov_transformed[4] = max_cov; // Y_Y
    cov_transformed[8] = max_cov; // Z_Z
    // Other elements remain 0.0
    
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
        
        // Check that offset correction was applied (no offset in default config)
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
        
        // Check that offset correction was applied
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
        
        // Check that covariance was calculated correctly
        let expected_angular_var = 0.03 * 0.03; // stddev^2
        assert_eq!(corrected_with_cov.angular_velocity_covariance[0], expected_angular_var); // xx
        assert_eq!(corrected_with_cov.angular_velocity_covariance[4], expected_angular_var); // yy
        assert_eq!(corrected_with_cov.angular_velocity_covariance[8], expected_angular_var); // zz
        
        let expected_accel_var = 10000.0 * 10000.0; // stddev^2
        assert_eq!(corrected_with_cov.linear_acceleration_covariance[0], expected_accel_var); // xx
        assert_eq!(corrected_with_cov.linear_acceleration_covariance[4], expected_accel_var); // yy
        assert_eq!(corrected_with_cov.linear_acceleration_covariance[8], expected_accel_var); // zz
    }

    #[test]
    fn test_transform_covariance() {
        let corrector = ImuCorrector::new();
        
        // Test covariance transformation (matches C++ transform_covariance function)
        let input_cov = [1.0, 0.5, 0.3, 0.5, 2.0, 0.4, 0.3, 0.4, 3.0]; // xx=1, yy=2, zz=3
        let transformed_cov = corrector.transform_covariance(&input_cov);
        
        // Should take maximum value (3.0) and apply to diagonal
        assert_eq!(transformed_cov[0], 3.0); // xx
        assert_eq!(transformed_cov[4], 3.0); // yy
        assert_eq!(transformed_cov[8], 3.0); // zz
        
        // Off-diagonal elements should be 0
        assert_eq!(transformed_cov[1], 0.0); // xy
        assert_eq!(transformed_cov[2], 0.0); // xz
        assert_eq!(transformed_cov[3], 0.0); // yx
        assert_eq!(transformed_cov[5], 0.0); // yz
        assert_eq!(transformed_cov[6], 0.0); // zx
        assert_eq!(transformed_cov[7], 0.0); // zy
    }

    #[test]
    fn test_public_transform_covariance() {
        // Test the public transform_covariance function
        let input_cov = [1.0, 0.5, 0.3, 0.5, 2.0, 0.4, 0.3, 0.4, 3.0]; // xx=1, yy=2, zz=3
        let transformed_cov = transform_covariance(&input_cov);
        
        // Should take maximum value (3.0) and apply to diagonal
        assert_eq!(transformed_cov[0], 3.0); // xx
        assert_eq!(transformed_cov[4], 3.0); // yy
        assert_eq!(transformed_cov[8], 3.0); // zz
        
        // Off-diagonal elements should be 0
        assert_eq!(transformed_cov[1], 0.0); // xy
        assert_eq!(transformed_cov[2], 0.0); // xz
        assert_eq!(transformed_cov[3], 0.0); // yx
        assert_eq!(transformed_cov[5], 0.0); // yz
        assert_eq!(transformed_cov[6], 0.0); // zx
        assert_eq!(transformed_cov[7], 0.0); // zy
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
        
        // Check that frame_id was updated
        assert_eq!(corrected_with_cov.header.frame_id, "base_link");
        
        // Check that covariance was transformed (should use max value)
        let expected_angular_var = 0.03 * 0.03; // stddev^2
        assert_eq!(corrected_with_cov.angular_velocity_covariance[0], expected_angular_var); // xx
        assert_eq!(corrected_with_cov.angular_velocity_covariance[4], expected_angular_var); // yy
        assert_eq!(corrected_with_cov.angular_velocity_covariance[8], expected_angular_var); // zz
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
        // Check that frame_id was updated
        assert_eq!(corrected_msg.header.frame_id, "base_link");
        
        // Check that translation was applied (linear acceleration should be transformed)
        // With translation of (1.0, 0.0, 0.0), the acceleration should be affected
        assert_eq!(corrected_msg.linear_acceleration.x, 9.8); // No change for identity rotation
    }

    #[test]
    fn test_imu_corrector_with_dynamic_tf_no_transform() {
        let transform_listener = MockTransformListener::new(); // Empty listener
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
        // Should return None when no transform is available
        assert!(corrected_msg.is_none());
    }
}
