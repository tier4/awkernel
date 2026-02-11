# EKF Localizer for awkernel

This is a no_std Rust implementation of the EKF (Extended Kalman Filter) Localizer for awkernel, extracted from Autoware's EKF Localizer.

## Features

- **no_std compatible**: Can run in embedded environments without standard library
- **TF publishing support**: Provides transform data for ROS2 tf broadcasting
- **EKF state estimation**: Estimates vehicle pose (x, y, yaw) and velocity (vx, wz)
- **Yaw bias estimation**: Optional yaw bias estimation for improved accuracy
- **Simple 1D filters**: For z, roll, and pitch estimation

## State Vector

The EKF state vector contains 6 elements:
- `x`: X position [m]
- `y`: Y position [m] 
- `yaw`: Yaw angle [rad]
- `yaw_bias`: Yaw bias [rad]
- `vx`: X velocity [m/s]
- `wz`: Z angular velocity [rad/s]

## Usage

### Basic Usage

```rust
use ekf_localizer::{EKFModule, EKFParameters, Pose, Transform, Point3D, Quaternion};

// Create EKF parameters
let params = EKFParameters::default();

// Create EKF module
let mut ekf = EKFModule::new(params);

// Initialize with initial pose
let initial_pose = Pose {
    position: Point3D { x: 0.0, y: 0.0, z: 0.0 },
    orientation: Quaternion { x: 0.0, y: 0.0, z: 0.0, w: 1.0 },
};

let transform = Transform {
    translation: Point3D { x: 0.0, y: 0.0, z: 0.0 },
    rotation: Quaternion { x: 0.0, y: 0.0, z: 0.0, w: 1.0 },
};

ekf.initialize(initial_pose, transform);

// Prediction step
ekf.predict(0.01); // dt = 10ms

// Get current pose for tf publishing
let pose = ekf.get_current_pose(false);
let transform = ekf.get_transform("base_link");

// Get covariance for uncertainty representation
let pose_covariance = ekf.get_current_pose_covariance();
let twist_covariance = ekf.get_current_twist_covariance();
```

### TF Publishing

To publish transforms for ROS2 tf, use the `get_transform` method:

```rust
// Get transform from map to base_link
let transform = ekf.get_transform("base_link");

// The transform contains:
// - translation: (x, y, z) position
// - rotation: quaternion orientation

// Use this data to publish tf2_msgs/TransformStamped
```

### Integration with awkernel Reactor API

The EKF module is designed to be used with awkernel's reactor API. You can create a separate file for pub/sub implementation:

```rust
// In your reactor implementation file
use ekf_localizer::EKFModule;

pub struct EKFLocalizerReactor {
    ekf: EKFModule,
    // Add other fields for pub/sub
}

impl EKFLocalizerReactor {
    pub fn new() -> Self {
        let params = EKFParameters::default();
        let ekf = EKFModule::new(params);
        
        Self {
            ekf,
            // Initialize other fields
        }
    }
    
    pub fn timer_callback(&mut self) {
        // Predict step
        self.ekf.predict(0.01);
        
        // Get transform for publishing
        let transform = self.ekf.get_transform("base_link");
        
        // Publish transform using awkernel reactor API
        // self.publish_tf(transform);
    }
}
```

## Parameters

Key parameters that can be tuned:

- `enable_yaw_bias_estimation`: Enable/disable yaw bias estimation
- `extend_state_step`: Number of extended state steps for delay compensation
- `proc_stddev_vx_c`: Process noise standard deviation for velocity
- `proc_stddev_wz_c`: Process noise standard deviation for angular velocity  
- `proc_stddev_yaw_c`: Process noise standard deviation for yaw
- `z_filter_proc_dev`: Process noise for z filter
- `roll_filter_proc_dev`: Process noise for roll filter
- `pitch_filter_proc_dev`: Process noise for pitch filter

## Dependencies

- `libm`: Mathematical functions for no_std
- `nalgebra`: Linear algebra operations
- `approx`: Approximate equality comparisons for tests

## Building

```bash
cd ~/azumi-lab/awkernel_1/ekf_localizer
cargo build --target thumbv7em-none-eabihf  # For ARM Cortex-M4
```

## Testing

```bash
cargo test
```

## Notes

- This implementation focuses on the core EKF calculation and tf generation
- Pub/sub functionality should be implemented separately using awkernel's reactor API
- The original Autoware implementation includes additional features like measurement updates, diagnostics, etc.
- This version is simplified for embedded use but maintains the essential EKF functionality 