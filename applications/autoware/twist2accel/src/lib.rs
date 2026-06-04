//! Twist-to-acceleration converter.
//!
//! Computes linear and angular acceleration via finite differences of
//! consecutive twist measurements, then applies per-axis 1-D low-pass
//! filtering.
//!
//! Mirrors the two-callback design of autoware_twist2accel/twist2accel.cpp:
//!   - `on_odom`  → processes KinematicState (Odometry) input when `use_odom = true`
//!   - `on_twist` → processes TwistWithCovariance input   when `use_odom = false`
//! Both convert the selected input to a (timestamp, Twist) pair and call the
//! shared `estimate_accel` logic — matching `estimate_accel()` in the C++ source.
#![no_std]

use awkernel_lib::{
    sync::{mcs::MCSNode, mutex::Mutex},
    time::Time,
};
use localization_types::{AccelWithCovarianceStamped, Header, KinematicState, TwistWithCovariance};

const LOWPASS_GAIN: f64 = 0.9;

// ---------------------------------------------------------------------------
// 1-D low-pass filter  (x[n] = g * x[n-1] + (1-g) * u[n])
// ---------------------------------------------------------------------------

struct LowpassFilter1D {
    gain: f64,
    prev_x: Option<f64>,
}

impl LowpassFilter1D {
    const fn new(gain: f64) -> Self {
        Self { gain, prev_x: None }
    }

    fn filter(&mut self, value: f64) -> f64 {
        let ret = match self.prev_x {
            Some(prev) => self.gain * prev + (1.0 - self.gain) * value,
            None => value,
        };
        self.prev_x = Some(ret);
        ret
    }
}

// ---------------------------------------------------------------------------
// Module state
// ---------------------------------------------------------------------------

struct Twist2AccelState {
    /// Selects input: true = KinematicState (odom), false = TwistWithCovariance.
    /// Mirrors `use_odom_` in the C++ node.
    use_odom: bool,
    /// Timestamp of the last processed sample (`Time::zero()` ≡ no previous sample).
    /// Mirrors `prev_twist_ptr_ != nullptr` guard in `estimate_accel()`.
    prev_stamp: Time,
    prev_linear_x: f64,
    prev_linear_y: f64,
    prev_linear_z: f64,
    prev_angular_x: f64,
    prev_angular_y: f64,
    prev_angular_z: f64,
    filter_lx: LowpassFilter1D,
    filter_ly: LowpassFilter1D,
    filter_lz: LowpassFilter1D,
    filter_ax: LowpassFilter1D,
    filter_ay: LowpassFilter1D,
    filter_az: LowpassFilter1D,
}

impl Twist2AccelState {
    const fn new() -> Self {
        Self {
            use_odom: true,
            prev_stamp: Time::zero(),
            prev_linear_x: 0.0,
            prev_linear_y: 0.0,
            prev_linear_z: 0.0,
            prev_angular_x: 0.0,
            prev_angular_y: 0.0,
            prev_angular_z: 0.0,
            filter_lx: LowpassFilter1D::new(LOWPASS_GAIN),
            filter_ly: LowpassFilter1D::new(LOWPASS_GAIN),
            filter_lz: LowpassFilter1D::new(LOWPASS_GAIN),
            filter_ax: LowpassFilter1D::new(LOWPASS_GAIN),
            filter_ay: LowpassFilter1D::new(LOWPASS_GAIN),
            filter_az: LowpassFilter1D::new(LOWPASS_GAIN),
        }
    }
}

static STATE: Mutex<Twist2AccelState> = Mutex::new(Twist2AccelState::new());

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Set whether odometry (`true`) or twist-with-covariance (`false`) drives
/// acceleration estimation.  Call once at node initialisation before the
/// first sensor message arrives.  Mirrors the `use_odom_` parameter.
pub fn configure(use_odom: bool) {
    let mut node = MCSNode::new();
    let mut state = STATE.lock(&mut node);
    state.use_odom = use_odom;
}

// ---------------------------------------------------------------------------
// Public entry points (mirror C++ callbacks)
// ---------------------------------------------------------------------------

/// Process a KinematicState (odometry) message.
///
/// Mirrors `callback_odometry` in twist2accel.cpp:
/// ```cpp
/// if (!use_odom_) return;
/// twist.header = msg->header; twist.twist = msg->twist.twist;
/// estimate_accel(twist);
/// ```
///
/// Returns `None` when `use_odom = false` (wrong input type — early return).
/// Returns `Some(accel)` otherwise; accel fields are zero on the first call
/// (no previous sample), matching the C++ behaviour where the message is
/// published even when `prev_twist_ptr_ == nullptr`.
pub fn on_odom(ks: &KinematicState) -> Option<AccelWithCovarianceStamped> {
    let mut node = MCSNode::new();
    let mut state = STATE.lock(&mut node);

    if !state.use_odom {
        return None;
    }

    Some(estimate_accel(
        &mut state,
        ks.header.time_stamp,
        ks.twist.twist.linear.x,
        ks.twist.twist.linear.y,
        ks.twist.twist.linear.z,
        ks.twist.twist.angular.x,
        ks.twist.twist.angular.y,
        ks.twist.twist.angular.z,
        ks.header.clone(),
    ))
}

/// Process a TwistWithCovariance message (e.g. from gyro_odometer).
///
/// Mirrors `callback_twist_with_covariance` in twist2accel.cpp:
/// ```cpp
/// if (use_odom_) return;
/// twist.header = msg->header; twist.twist = msg->twist.twist;
/// estimate_accel(twist);
/// ```
///
/// Returns `None` when `use_odom = true` (early return).
pub fn on_twist(
    header: &Header,
    twist: &TwistWithCovariance,
) -> Option<AccelWithCovarianceStamped> {
    let mut node = MCSNode::new();
    let mut state = STATE.lock(&mut node);

    if state.use_odom {
        return None;
    }

    Some(estimate_accel(
        &mut state,
        header.time_stamp,
        twist.twist.linear.x,
        twist.twist.linear.y,
        twist.twist.linear.z,
        twist.twist.angular.x,
        twist.twist.angular.y,
        twist.twist.angular.z,
        header.clone(),
    ))
}

// ---------------------------------------------------------------------------
// Shared inner computation (mirrors estimate_accel() in C++)
// ---------------------------------------------------------------------------

fn estimate_accel(
    state: &mut Twist2AccelState,
    curr_stamp: Time,
    lin_x: f64,
    lin_y: f64,
    lin_z: f64,
    ang_x: f64,
    ang_y: f64,
    ang_z: f64,
    out_header: Header,
) -> AccelWithCovarianceStamped {
    let mut out = AccelWithCovarianceStamped::default();
    out.header = out_header;

    if state.prev_stamp != Time::zero() {
        let dt = {
            let d = curr_stamp
                .saturating_duration_since(state.prev_stamp)
                .as_secs_f64();
            if d < 1.0e-3 { 1.0e-3 } else { d }
        };

        let alx = (lin_x - state.prev_linear_x) / dt;
        let aly = (lin_y - state.prev_linear_y) / dt;
        let alz = (lin_z - state.prev_linear_z) / dt;
        let aax = (ang_x - state.prev_angular_x) / dt;
        let aay = (ang_y - state.prev_angular_y) / dt;
        let aaz = (ang_z - state.prev_angular_z) / dt;

        out.accel.accel.linear.x = state.filter_lx.filter(alx);
        out.accel.accel.linear.y = state.filter_ly.filter(aly);
        out.accel.accel.linear.z = state.filter_lz.filter(alz);
        out.accel.accel.angular.x = state.filter_ax.filter(aax);
        out.accel.accel.angular.y = state.filter_ay.filter(aay);
        out.accel.accel.angular.z = state.filter_az.filter(aaz);

        out.accel.covariance[(0, 0)] = 1.0;
        out.accel.covariance[(1, 1)] = 1.0;
        out.accel.covariance[(2, 2)] = 1.0;
        out.accel.covariance[(3, 3)] = 0.05;
        out.accel.covariance[(4, 4)] = 0.05;
        out.accel.covariance[(5, 5)] = 0.05;
    }

    state.prev_stamp = curr_stamp;
    state.prev_linear_x = lin_x;
    state.prev_linear_y = lin_y;
    state.prev_linear_z = lin_z;
    state.prev_angular_x = ang_x;
    state.prev_angular_y = ang_y;
    state.prev_angular_z = ang_z;

    out
}
