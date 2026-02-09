#![no_std]
extern crate alloc;

use alloc::{borrow::Cow, collections::VecDeque, string::String, vec::Vec};
use core::time::Duration;
// Global instance and lazy initialization support
use core::sync::atomic::{AtomicPtr, Ordering as AtomicOrdering};
use core::ptr::null_mut;

// Re-export common types for consistency with other libraries
pub use imu_driver::{Header, Vector3, Quaternion, ImuMsg};
pub use vehicle_velocity_converter::{Odometry, TwistWithCovarianceStamped, TwistWithCovariance, Twist};
pub use imu_corrector::{ImuWithCovariance, Transform, transform_covariance};


static GYRO_ODOMETER_INSTANCE: AtomicPtr<GyroOdometerCore> = AtomicPtr::new(null_mut());

// Constants for covariance indices (matching C++ implementation)
const COV_IDX_X_X: usize = 0;
const COV_IDX_Y_Y: usize = 4;
const COV_IDX_Z_Z: usize = 8;

// XYZRPY covariance indices (matching C++ implementation)
const COV_IDX_XYZRPY_X_X: usize = 0;
const COV_IDX_XYZRPY_Y_Y: usize = 7;
const COV_IDX_XYZRPY_Z_Z: usize = 14;
const COV_IDX_XYZRPY_ROLL_ROLL: usize = 21;
const COV_IDX_XYZRPY_PITCH_PITCH: usize = 28;
const COV_IDX_XYZRPY_YAW_YAW: usize = 35;

// GyroOdometerCore implementation
pub struct GyroOdometerCore {
    // Parameters
    pub output_frame: String,
    pub message_timeout_sec: f64,

    // State
    pub vehicle_twist_arrived: bool,
    pub imu_arrived: bool,
    pub vehicle_twist_queue: VecDeque<TwistWithCovarianceStamped>,
    pub gyro_queue: VecDeque<ImuWithCovariance>,

    // Configuration
    pub config: GyroOdometerConfig,
}

impl GyroOdometerCore {
    pub fn new(config: GyroOdometerConfig) -> Result<Self> {
        let queue_size = config.queue_size;
        let output_frame = config.output_frame.clone();
        let message_timeout_sec = config.message_timeout_sec;
        
        Ok(Self {
            output_frame,
            message_timeout_sec,
            vehicle_twist_arrived: false,
            imu_arrived: false,
            vehicle_twist_queue: VecDeque::with_capacity(queue_size),
            gyro_queue: VecDeque::with_capacity(queue_size),
            config,
        })
    }



    /// Main processing function (matching C++ concat_gyro_and_odometer)
    /// 
    /// # Arguments
    /// * `current_time` - Current system time in nanoseconds (matching C++ this->now())
    pub fn concat_gyro_and_odometer(&mut self, current_time: u64) -> Result<Option<TwistWithCovarianceStamped>> {
        // Check if first messages have arrived (matching C++ implementation)
        if !self.vehicle_twist_arrived {
            self.vehicle_twist_queue.clear();
            self.gyro_queue.clear();
            return Ok(None);
        }
        if !self.imu_arrived {
            self.vehicle_twist_queue.clear();
            self.gyro_queue.clear();
            return Ok(None);
        }

        // Check timeout (matching C++ implementation)
        // C++: vehicle_twist_dt = std::abs((this->now() - latest_vehicle_twist_ros_time_).seconds())
        if !self.vehicle_twist_queue.is_empty() && !self.gyro_queue.is_empty() {
            let latest_vehicle_twist_stamp = self.vehicle_twist_queue.back().unwrap().header.timestamp;
            let latest_imu_stamp = self.gyro_queue.back().unwrap().header.timestamp;
            
            // Check vehicle twist timeout (matching C++ vehicle_twist_dt > message_timeout_sec_)
            if Self::check_timeout(current_time, latest_vehicle_twist_stamp, self.message_timeout_sec) {
                self.vehicle_twist_queue.clear();
                self.gyro_queue.clear();
                return Err(GyroOdometerError::TimeoutError(
                    String::from("Vehicle twist message timeout")
                ));
            }
            
            // Check IMU timeout (matching C++ imu_dt > message_timeout_sec_)
            if Self::check_timeout(current_time, latest_imu_stamp, self.message_timeout_sec) {
                self.vehicle_twist_queue.clear();
                self.gyro_queue.clear();
                return Err(GyroOdometerError::TimeoutError(
                    String::from("IMU message timeout")
                ));
            }
        }

        // Check queue size (matching C++ implementation)
        if self.vehicle_twist_queue.is_empty() || self.gyro_queue.is_empty() {
            return Ok(None);
        }

        // Get transformation (matching C++ implementation)
        let tf = self.get_transform(
            &self.gyro_queue.front().unwrap().header.frame_id,
            &self.output_frame,
        )?;

        // Transform gyro frame (matching C++ implementation)
        for gyro in &mut self.gyro_queue {
            let transformed_angular_velocity = tf.apply_to_vector(gyro.angular_velocity.clone());
            // Note: In C++ implementation, frame_id is updated to output_frame
            // but for now we keep the original frame_id to avoid lifetime issues
            gyro.angular_velocity = transformed_angular_velocity;
            // Covariance is already calculated and transformed by imu_corrector
        }

        // Calculate mean and covariance (matching C++ implementation exactly)
        let mut vx_mean = 0.0;
        let mut gyro_mean = Vector3::new(0.0, 0.0, 0.0);
        let mut vx_covariance_original = 0.0;
        let mut gyro_covariance_original = Vector3::new(0.0, 0.0, 0.0);

        // Calculate vehicle twist mean and covariance
        for vehicle_twist in &self.vehicle_twist_queue {
            vx_mean += vehicle_twist.twist.twist.linear.x;
            vx_covariance_original += vehicle_twist.twist.covariance[0 * 6 + 0];
        }
        vx_mean /= self.vehicle_twist_queue.len() as f64;
        vx_covariance_original /= self.vehicle_twist_queue.len() as f64;

        // Calculate gyro mean and covariance (using pre-calculated covariance from imu_corrector)
        for gyro in &self.gyro_queue {
            gyro_mean.x += gyro.angular_velocity.x;
            gyro_mean.y += gyro.angular_velocity.y;
            gyro_mean.z += gyro.angular_velocity.z;
            // Use pre-calculated covariance from imu_corrector (already transformed)
            gyro_covariance_original.x += gyro.angular_velocity_covariance[COV_IDX_X_X];
            gyro_covariance_original.y += gyro.angular_velocity_covariance[COV_IDX_Y_Y];
            gyro_covariance_original.z += gyro.angular_velocity_covariance[COV_IDX_Z_Z];
        }
        gyro_mean.x /= self.gyro_queue.len() as f64;
        gyro_mean.y /= self.gyro_queue.len() as f64;
        gyro_mean.z /= self.gyro_queue.len() as f64;
        gyro_covariance_original.x /= self.gyro_queue.len() as f64;
        gyro_covariance_original.y /= self.gyro_queue.len() as f64;
        gyro_covariance_original.z /= self.gyro_queue.len() as f64;

        // Create result (matching C++ implementation)
        let latest_vehicle_twist_stamp = self.vehicle_twist_queue.back().unwrap().header.timestamp;
        let latest_imu_stamp = self.gyro_queue.back().unwrap().header.timestamp;
        
        let result_timestamp = if latest_vehicle_twist_stamp < latest_imu_stamp {
            latest_imu_stamp
        } else {
            latest_vehicle_twist_stamp
        };

        let mut result = TwistWithCovarianceStamped {
            header: Header {
                frame_id: self.gyro_queue.front().unwrap().header.frame_id,
                timestamp: result_timestamp,
            },
            twist: TwistWithCovariance {
                twist: Twist {
                    linear: Vector3::new(vx_mean, 0.0, 0.0),
                    angular: gyro_mean,
                },
                covariance: [0.0; 36],
            },
        };

        // Set covariance (matching C++ implementation exactly)
        result.twist.covariance[COV_IDX_XYZRPY_X_X] = 
            vx_covariance_original / self.vehicle_twist_queue.len() as f64;
        result.twist.covariance[COV_IDX_XYZRPY_Y_Y] = 100000.0;
        result.twist.covariance[COV_IDX_XYZRPY_Z_Z] = 100000.0;
        result.twist.covariance[COV_IDX_XYZRPY_ROLL_ROLL] = 
            gyro_covariance_original.x / self.gyro_queue.len() as f64;
        result.twist.covariance[COV_IDX_XYZRPY_PITCH_PITCH] = 
            gyro_covariance_original.y / self.gyro_queue.len() as f64;
        result.twist.covariance[COV_IDX_XYZRPY_YAW_YAW] = 
            gyro_covariance_original.z / self.gyro_queue.len() as f64;

        // Clear queues (matching C++ implementation)
        self.vehicle_twist_queue.clear();
        self.gyro_queue.clear();

        Ok(Some(result))
    }

    /// Check timeout (matching C++ implementation)
    // Timeout checking function (matching C++ implementation)
    pub fn check_timeout(current_timestamp: u64, last_timestamp: u64, timeout_sec: f64) -> bool {
        let dt = (current_timestamp as f64 - last_timestamp as f64) / 1_000_000_000.0; // Convert to seconds
        dt.abs() > timeout_sec
    }

    /// Get transform (to be implemented by the caller)
    /// Returns identity transform by default. Override this behavior by providing transform externally.
    pub fn get_transform(&self, from_frame: &str, to_frame: &str) -> Result<Transform> {
        // This should be implemented by the caller (e.g., transform listener)
        // For now, return identity transform
        if from_frame == to_frame || from_frame == "" || to_frame == "" {
            Ok(Transform::identity())
        } else {
            // In a real implementation, this would query the transform tree
            // For awkernel, we assume all frames are aligned (identity transform)
            Ok(Transform::identity())
        }
    }

    /// Process result and apply vehicle stop logic
    pub fn process_result(&self, twist_with_cov_raw: TwistWithCovarianceStamped) -> TwistWithCovarianceStamped {
        // 車両が停止している場合の処理 (matching C++ implementation exactly)
        if twist_with_cov_raw.twist.twist.angular.z.abs() < 0.01
            && twist_with_cov_raw.twist.twist.linear.x.abs() < 0.01
        {
            let mut twist = twist_with_cov_raw;
            twist.twist.twist.angular.x = 0.0;
            twist.twist.twist.angular.y = 0.0;
            twist.twist.twist.angular.z = 0.0;
            twist
        } else {
            twist_with_cov_raw
        }
    }

    /// Convert vehicle velocity data to twist format
    pub fn convert_vehicle_velocity_to_twist(&self, odometry: &Odometry, timestamp: u64) -> TwistWithCovarianceStamped {
        TwistWithCovarianceStamped {
            header: Header {
                frame_id: "base_link",
                timestamp,
            },
            twist: TwistWithCovariance {
                twist: Twist {
                    linear: Vector3::new(odometry.velocity, 0.0, 0.0),
                    angular: Vector3::new(0.0, 0.0, 0.0),
                },
                covariance: [0.0; 36],
            },
        }
    }

    /// Add vehicle twist to queue (matching test_autoware usage pattern)
    pub fn add_vehicle_twist(&mut self, twist: TwistWithCovarianceStamped) {
        self.vehicle_twist_arrived = true;
        self.vehicle_twist_queue.push_back(twist);
    }

    /// Add IMU data to queue (matching test_autoware usage pattern)
    pub fn add_imu(&mut self, imu: ImuWithCovariance) {
        self.imu_arrived = true;
        self.gyro_queue.push_back(imu);
    }

    /// Process queues and get result (matching test_autoware process_queues_and_get_result)
    pub fn process_and_get_result(&mut self, current_time: u64) -> Option<TwistWithCovarianceStamped> {
        match self.concat_gyro_and_odometer(current_time) {
            Ok(result) => result,
            Err(_) => None,
        }
    }

    /// Get queue sizes
    pub fn get_queue_sizes(&self) -> (usize, usize) {
        (self.vehicle_twist_queue.len(), self.gyro_queue.len())
    }

    /// Clear both queues
    pub fn clear_queues(&mut self) {
        self.vehicle_twist_queue.clear();
        self.gyro_queue.clear();
    }

    /// Reset arrival flags
    pub fn reset_arrival_flags(&mut self) {
        self.vehicle_twist_arrived = false;
        self.imu_arrived = false;
    }
}

#[derive(Debug)]
pub enum GyroOdometerError {
    TransformError(String),
    TimeoutError(String),
    QueueError(String),
    ParameterError(String),
}

impl core::fmt::Display for GyroOdometerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            GyroOdometerError::TransformError(msg) => write!(f, "Transform error: {}", msg),
            GyroOdometerError::TimeoutError(msg) => write!(f, "Timeout error: {}", msg),
            GyroOdometerError::QueueError(msg) => write!(f, "Queue error: {}", msg),
            GyroOdometerError::ParameterError(msg) => write!(f, "Invalid parameter: {}", msg),
        }
    }
}

impl core::error::Error for GyroOdometerError {}

type Result<T> = core::result::Result<T, GyroOdometerError>;

#[derive(Debug, Clone)]
pub struct GyroOdometerConfig {
    pub output_frame: String,
    pub message_timeout_sec: f64,
    pub queue_size: usize,
    pub transform_timeout: Duration,
    pub min_velocity_threshold: f64,
    pub covariance_scale: f64,
}

impl Default for GyroOdometerConfig {
    fn default() -> Self {
        Self {
            output_frame: String::from("base_link"),
            message_timeout_sec: 1.0,
            queue_size: 100,
            transform_timeout: Duration::from_secs(1),
            min_velocity_threshold: 0.01,
            covariance_scale: 100000.0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gyro_odometer_core_creation() {
        let config = GyroOdometerConfig::default();
        let core = GyroOdometerCore::new(config);
        assert!(core.is_ok());
    }

    #[test]
    fn test_imu_with_covariance_conversion() {
        let imu_msg = ImuMsg {
            header: Header {
                frame_id: "imu_link",
                timestamp: 123456789,
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

        let imu_with_cov = ImuWithCovariance::from_imu_msg(&imu_msg);
        let converted_back = imu_with_cov.to_imu_msg();

        assert_eq!(imu_msg.header.frame_id, converted_back.header.frame_id);
        assert_eq!(imu_msg.header.timestamp, converted_back.header.timestamp);
        assert_eq!(imu_msg.angular_velocity.x, converted_back.angular_velocity.x);
        assert_eq!(imu_msg.angular_velocity.y, converted_back.angular_velocity.y);
        assert_eq!(imu_msg.angular_velocity.z, converted_back.angular_velocity.z);
    }

    #[test]
    fn test_vehicle_velocity_conversion() {
        let config = GyroOdometerConfig::default();
        let core = GyroOdometerCore::new(config).unwrap();
        
        let odometry = Odometry { velocity: 15.5 };
        let twist = core.convert_vehicle_velocity_to_twist(&odometry, 123456789);
        
        assert_eq!(twist.header.frame_id, "base_link");
        assert_eq!(twist.header.timestamp, 123456789);
        assert_eq!(twist.twist.twist.linear.x, 15.5);
        assert_eq!(twist.twist.twist.linear.y, 0.0);
        assert_eq!(twist.twist.twist.linear.z, 0.0);
    }

    #[test]
    fn test_imu_corrector_integration() {
        let config = GyroOdometerConfig::default();
        let mut core = GyroOdometerCore::new(config).unwrap();
        
        // Create IMU with covariance from imu_corrector
        let imu_with_cov = ImuWithCovariance {
            header: Header {
                frame_id: "imu_link",
                timestamp: 123456789,
            },
            orientation: Quaternion {
                x: 0.0,
                y: 0.0,
                z: 0.0,
                w: 1.0,
            },
            angular_velocity: Vector3::new(0.1, 0.2, 0.3),
            angular_velocity_covariance: [0.0009, 0.0, 0.0, 0.0, 0.0009, 0.0, 0.0, 0.0, 0.0009], // 0.03^2
            linear_acceleration: Vector3::new(9.8, 0.0, 0.0),
            linear_acceleration_covariance: [100000000.0, 0.0, 0.0, 0.0, 100000000.0, 0.0, 0.0, 0.0, 100000000.0], // 10000^2
        };

        // Process IMU with covariance
        let result = core.process_imu_with_covariance(imu_with_cov);
        assert!(result.is_ok());
    }

    #[test]
    fn test_transform_covariance_from_imu_corrector() {
        // Test that we can use the transform_covariance function from imu_corrector
        let input = [1.0, 0.0, 0.0, 0.0, 2.0, 0.0, 0.0, 0.0, 3.0];
        let output = transform_covariance(&input);
        assert_eq!(output[COV_IDX_X_X], 3.0);
        assert_eq!(output[COV_IDX_Y_Y], 3.0);
        assert_eq!(output[COV_IDX_Z_Z], 3.0);
    }
}

/// Get or initialize the global GyroOdometerCore instance
/// This provides lazy initialization with thread-safe access
pub fn get_or_initialize() -> Result<&'static mut GyroOdometerCore> {
    let ptr = GYRO_ODOMETER_INSTANCE.load(AtomicOrdering::Acquire);
    
    if !ptr.is_null() {
        return Ok(unsafe { &mut *ptr });
    }
    
    // Not initialized, try to initialize
    let config = GyroOdometerConfig::default();
    let core = GyroOdometerCore::new(config)?;
    
    // Allocate on heap and store pointer
    let boxed_core = alloc::boxed::Box::new(core);
    let new_ptr = alloc::boxed::Box::into_raw(boxed_core);
    
    // Try to store the pointer atomically
    match GYRO_ODOMETER_INSTANCE.compare_exchange(
        null_mut(),
        new_ptr,
        AtomicOrdering::Acquire,
        AtomicOrdering::Relaxed,
    ) {
        Ok(_) => {
            // We successfully initialized
            Ok(unsafe { &mut *new_ptr })
        }
        Err(existing_ptr) => {
            // Another thread already initialized it, clean up our allocation
            unsafe {
                let _ = alloc::boxed::Box::from_raw(new_ptr);
            }
            Ok(unsafe { &mut *existing_ptr })
        }
    }
}