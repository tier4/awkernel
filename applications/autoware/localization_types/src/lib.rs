//! Shared localization message types, mirroring TECS tecs_global.rs definitions.
//! Types use nalgebra for linear algebra and heapless for fixed-size strings.
#![no_std]

pub use awkernel_lib::time::Time;

// ---------------------------------------------------------------------------
// Header
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct Header {
    pub time_stamp: Time,
    pub frame_id: heapless::String<256>,
}

impl Header {
    pub const fn new() -> Self {
        Self {
            time_stamp: Time::zero(),
            frame_id: heapless::String::new(),
        }
    }
}

impl Default for Header {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Geometry primitives
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct Pose {
    /// Position in 3D space.
    pub point: nalgebra::Vector3<f64>,
    /// Orientation as a unit quaternion (w, i, j, k).
    pub orientation: nalgebra::Quaternion<f64>,
}

impl Pose {
    pub const fn new() -> Self {
        Self {
            point: nalgebra::Vector3::new(0.0, 0.0, 0.0),
            orientation: nalgebra::Quaternion::new(1.0, 0.0, 0.0, 0.0),
        }
    }
}

impl Default for Pose {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone)]
pub struct PoseWithCovariance {
    pub pose: Pose,
    pub covariance: nalgebra::Matrix6<f64>,
}

impl Default for PoseWithCovariance {
    fn default() -> Self {
        Self {
            pose: Pose::default(),
            covariance: nalgebra::Matrix6::zeros(),
        }
    }
}

#[derive(Clone)]
pub struct Twist {
    pub linear: nalgebra::Vector3<f64>,
    pub angular: nalgebra::Vector3<f64>,
}

impl Twist {
    pub const fn new() -> Self {
        Self {
            linear: nalgebra::Vector3::new(0.0, 0.0, 0.0),
            angular: nalgebra::Vector3::new(0.0, 0.0, 0.0),
        }
    }
}

impl Default for Twist {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone)]
pub struct TwistWithCovariance {
    pub twist: Twist,
    pub covariance: nalgebra::Matrix6<f64>,
}

impl Default for TwistWithCovariance {
    fn default() -> Self {
        Self {
            twist: Twist::default(),
            covariance: nalgebra::Matrix6::zeros(),
        }
    }
}

#[derive(Clone)]
pub struct Accel {
    pub linear: nalgebra::Vector3<f64>,
    pub angular: nalgebra::Vector3<f64>,
}

impl Accel {
    pub const fn new() -> Self {
        Self {
            linear: nalgebra::Vector3::new(0.0, 0.0, 0.0),
            angular: nalgebra::Vector3::new(0.0, 0.0, 0.0),
        }
    }
}

impl Default for Accel {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone)]
pub struct AccelWithCovariance {
    pub accel: Accel,
    pub covariance: nalgebra::Matrix6<f64>,
}

impl Default for AccelWithCovariance {
    fn default() -> Self {
        Self {
            accel: Accel::default(),
            covariance: nalgebra::Matrix6::zeros(),
        }
    }
}

// ---------------------------------------------------------------------------
// Composite messages
// ---------------------------------------------------------------------------

/// Unified localization state: pose + twist + accel with covariances.
/// Corresponds to TECS KinematicState / Autoware Odometry (extended).
#[derive(Clone)]
pub struct KinematicState {
    pub header: Header,
    pub child_frame_id: heapless::String<256>,
    pub pose: PoseWithCovariance,
    pub twist: TwistWithCovariance,
    pub accel: AccelWithCovariance,
}

impl Default for KinematicState {
    fn default() -> Self {
        Self {
            header: Header::default(),
            child_frame_id: heapless::String::new(),
            pose: PoseWithCovariance::default(),
            twist: TwistWithCovariance::default(),
            accel: AccelWithCovariance::default(),
        }
    }
}

#[derive(Clone)]
pub struct AccelWithCovarianceStamped {
    pub header: Header,
    pub accel: AccelWithCovariance,
}

impl Default for AccelWithCovarianceStamped {
    fn default() -> Self {
        Self {
            header: Header::default(),
            accel: AccelWithCovariance::default(),
        }
    }
}

// ---------------------------------------------------------------------------
// Control output
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct Lateral {
    pub stamp: Time,
    pub control_time: Time,
    pub steering_tire_angle: f64,
    pub steering_tire_rotation_rate: f64,
    pub is_defined_steering_tire_rotation_rate: bool,
}

impl Default for Lateral {
    fn default() -> Self {
        Self {
            stamp: Time::zero(),
            control_time: Time::zero(),
            steering_tire_angle: 0.0,
            steering_tire_rotation_rate: 0.0,
            is_defined_steering_tire_rotation_rate: false,
        }
    }
}

#[derive(Clone)]
pub struct Longitudinal {
    pub stamp: Time,
    pub control_time: Time,
    pub velocity: f64,
    pub acceleration: f64,
    pub jerk: f64,
    pub is_defined_acceleration: bool,
    pub is_defined_jerk: bool,
}

impl Default for Longitudinal {
    fn default() -> Self {
        Self {
            stamp: Time::zero(),
            control_time: Time::zero(),
            velocity: 0.0,
            acceleration: 0.0,
            jerk: 0.0,
            is_defined_acceleration: false,
            is_defined_jerk: false,
        }
    }
}

#[derive(Clone)]
pub struct Control {
    pub stamp: Time,
    pub control_time: Time,
    pub lateral: Lateral,
    pub longitudinal: Longitudinal,
}

impl Default for Control {
    fn default() -> Self {
        Self {
            stamp: Time::zero(),
            control_time: Time::zero(),
            lateral: Lateral::default(),
            longitudinal: Longitudinal::default(),
        }
    }
}

// ---------------------------------------------------------------------------
// Trajectory
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct TrajectoryPoint {
    pub pose: Pose,
    pub longitudinal_velocity_mps: f64,
}

impl TrajectoryPoint {
    pub const fn new(
        x: f64,
        y: f64,
        z: f64,
        qw: f64,
        qi: f64,
        qj: f64,
        qk: f64,
        vel: f64,
    ) -> Self {
        Self {
            pose: Pose {
                point: nalgebra::Vector3::new(x, y, z),
                orientation: nalgebra::Quaternion::new(qw, qi, qj, qk),
            },
            longitudinal_velocity_mps: vel,
        }
    }
}
