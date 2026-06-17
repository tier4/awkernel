//! Control command gate: speed-dependent safety filter for Control commands.
//!
//! Ported from autoware_universe/control/autoware_control_command_gate
//! (VehicleCmdFilter + CommandFilter).
//!
//! ## Excluded from universe implementation
//! - CommandSelector       — DAG enforces single publisher per topic; no runtime source switching
//! - Compatibility layer   — legacy vehicle_cmd_gate ADapi/emergency interfaces; no counterpart in awkernel
//! - Transition filter     — only needed for source switching via CommandSelector
//! - TimeoutDiag           — no diagnostics framework in no_std
//! - Timer-driven resend   — DAG is message-driven; heartbeat re-send is unnecessary
//! - GearCommand / TurnIndicators / HazardLights — different domain, out of scope
//! - checkIsActivated      — debug diagnostic output, excluded with diagnostics
//! - is_autoware_control_enabled branch — awkernel is always in autonomous mode; the manual-mode
//!   prev_cmd override (current_status_as_command) can never fire
#![no_std]

use awkernel_lib::sync::{mcs::MCSNode, mutex::Mutex};
use awkernel_lib::time::Time;
use localization_types::{Control, KinematicState};

// ---------------------------------------------------------------------------
// Speed-dependent limit array (replaces std::vector<double>)
// ---------------------------------------------------------------------------

const MAX_SPEED_POINTS: usize = 16;
type LimitArray = heapless::Vec<f64, MAX_SPEED_POINTS>;

// ---------------------------------------------------------------------------
// Public filter parameters  (mirrors VehicleCmdFilterParam)
// ---------------------------------------------------------------------------

pub struct FilterParams {
    pub wheel_base: f64,
    pub vel_lim: f64,
    /// Reference speeds [m/s] for interpolation. All limit arrays must be the same length.
    pub reference_speed_points: LimitArray,
    pub lon_acc_lim_for_lon_vel: LimitArray,
    pub lon_jerk_lim_for_lon_acc: LimitArray,
    pub lat_acc_lim_for_steer_cmd: LimitArray,
    pub lat_jerk_lim_for_steer_cmd: LimitArray,
    pub steer_cmd_lim: LimitArray,
    pub steer_rate_lim_for_steer_cmd: LimitArray,
    pub steer_cmd_diff_lim_from_current_steer: LimitArray,
    /// Scalar lateral jerk limit used for steer-rate cap (not speed-dependent).
    pub lat_jerk_lim_for_steer_rate: f64,
}

// ---------------------------------------------------------------------------
// Internal state (None until configure() is called → pass-through)
// ---------------------------------------------------------------------------

struct FilterState {
    params: FilterParams,
    enable: bool,
    prev_cmd: Control,
    prev_time: Option<Time>,
}

static STATE: Mutex<Option<FilterState>> = Mutex::new(None);

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Set filter parameters. Must be called once at node initialisation.
/// `enable` mirrors `enable_command_limit_filter` ROS parameter.
pub fn configure(params: FilterParams, enable: bool) {
    let mut node = MCSNode::new();
    let mut st = STATE.lock(&mut node);
    *st = Some(FilterState {
        params,
        enable,
        prev_cmd: Control::default(),
        prev_time: None,
    });
}

/// Filter a Control command using speed-dependent safety limits.
///
/// `ks.twist.twist.linear.x` is used as current longitudinal speed.
/// Current steering angle is proxied from the previous filtered command
/// (`prev_cmd.lateral.steering_tire_angle`) because SteeringReport is not
/// yet wired into the awkernel DAG.
///
/// Returns the input unchanged if configure() has not been called or
/// `enable` is false.
pub fn filter(ctrl: &Control, ks: &KinematicState) -> Control {
    let mut node = MCSNode::new();
    let mut st = STATE.lock(&mut node);
    let state = match st.as_mut() {
        None => return ctrl.clone(),
        Some(s) => s,
    };
    if !state.enable {
        return ctrl.clone();
    }

    let current_vel = ks.twist.twist.linear.x;
    // Proxy: no SteeringReport in DAG yet. Add explicit input when wired.
    let current_steer = state.prev_cmd.lateral.steering_tire_angle;

    let now = Time::now();
    let dt = match state.prev_time {
        None => 0.0,
        Some(prev) => now.saturating_duration_since(prev).as_secs_f64(),
    };
    state.prev_time = Some(now);

    let out = filter_all(ctrl, &state.params, &state.prev_cmd, current_vel, current_steer, dt);

    // Always use filtered output as prev_cmd: awkernel is always in autonomous mode,
    // so the manual-mode branch (use actual vehicle status as prev) never applies.
    state.prev_cmd = out.clone();
    out
}

// ---------------------------------------------------------------------------
// filterAll — mirrors VehicleCmdFilter::filterAll() call order exactly
// ---------------------------------------------------------------------------

fn filter_all(
    cmd: &Control,
    params: &FilterParams,
    prev_cmd: &Control,
    current_vel: f64,
    current_steer: f64,
    dt: f64,
) -> Control {
    let mut out = cmd.clone();
    limit_lateral_steer(&mut out, params, current_vel);
    limit_lateral_steer_rate(&mut out, params, prev_cmd, current_vel, dt);
    limit_longitudinal_with_jerk(&mut out, params, prev_cmd, current_vel, dt);
    limit_longitudinal_with_acc(&mut out, params, prev_cmd, current_vel, dt);
    limit_longitudinal_with_vel(&mut out, params);
    limit_lateral_with_lat_jerk(&mut out, params, prev_cmd, current_vel, dt);
    limit_lateral_with_lat_acc(&mut out, params, current_vel);
    limit_actual_steer_diff(&mut out, params, current_vel, current_steer);
    out
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Linear interpolation of a limit array against reference speed points.
/// Uses zero-order hold outside the reference range.
/// Returns f64::MAX (no limit) if either array is empty.
fn interpolate_from_speed(limits: &LimitArray, reference: &LimitArray, current_speed: f64) -> f64 {
    if limits.is_empty() || reference.is_empty() {
        return f64::MAX;
    }
    let current = libm::fabs(current_speed);
    let last = reference.len() - 1;
    if current <= reference[0] {
        return limits[0];
    }
    if current >= reference[last] {
        return limits[last];
    }
    for i in 0..last {
        if reference[i] <= current && current <= reference[i + 1] {
            let denom = (reference[i + 1] - reference[i]).max(1.0e-5);
            let ratio = ((current - reference[i]) / denom).max(0.0).min(1.0);
            return limits[i] + ratio * (limits[i + 1] - limits[i]);
        }
    }
    limits[last]
}

fn limit_diff(curr: f64, prev: f64, diff_lim: f64) -> f64 {
    let diff = (curr - prev).max(-diff_lim).min(diff_lim);
    prev + diff
}

/// Lateral acceleration from steering angle and speed: a_y = v² tan(δ) / L
fn calc_lat_acc(steer: f64, vel: f64, wheel_base: f64) -> f64 {
    vel * vel * libm::tan(steer) / wheel_base
}

fn calc_steer_from_latacc(v: f64, latacc: f64, wheel_base: f64) -> f64 {
    let v_sq = (v * v).max(0.001);
    libm::atan(latacc * wheel_base / v_sq)
}

// ---------------------------------------------------------------------------
// Limit functions (mirror VehicleCmdFilter methods)
// ---------------------------------------------------------------------------

/// Clamp steering angle to ±steer_cmd_lim.
/// Hard-capped to ±π/2: tan/atan calculations are undefined beyond that.
fn limit_lateral_steer(cmd: &mut Control, params: &FilterParams, current_vel: f64) {
    let raw_lim = interpolate_from_speed(
        &params.steer_cmd_lim,
        &params.reference_speed_points,
        current_vel,
    )
    .abs();
    let steer_lim = raw_lim.min(core::f64::consts::FRAC_PI_2);
    cmd.lateral.steering_tire_angle =
        cmd.lateral.steering_tire_angle.max(-steer_lim).min(steer_lim);
}

/// Clamp steering rate and steering angle change per dt.
/// Effective rate = min(steer_rate_lim, lat_jerk_lim / v²).
fn limit_lateral_steer_rate(
    cmd: &mut Control,
    params: &FilterParams,
    prev_cmd: &Control,
    current_vel: f64,
    dt: f64,
) {
    let cmd_rate_lim = interpolate_from_speed(
        &params.steer_rate_lim_for_steer_cmd,
        &params.reference_speed_points,
        current_vel,
    );
    let v_sq = (current_vel * current_vel).max(0.001);
    let jerk_rate_lim = params.lat_jerk_lim_for_steer_rate * params.wheel_base / v_sq;
    let eff_rate_lim = cmd_rate_lim.min(jerk_rate_lim);

    cmd.lateral.steering_tire_rotation_rate = cmd
        .lateral
        .steering_tire_rotation_rate
        .max(-eff_rate_lim)
        .min(eff_rate_lim);

    let steer_diff_lim = eff_rate_lim * dt;
    let ds = (cmd.lateral.steering_tire_angle - prev_cmd.lateral.steering_tire_angle)
        .max(-steer_diff_lim)
        .min(steer_diff_lim);
    cmd.lateral.steering_tire_angle = prev_cmd.lateral.steering_tire_angle + ds;
}

/// Clamp longitudinal jerk and limit acceleration change by jerk × dt.
fn limit_longitudinal_with_jerk(
    cmd: &mut Control,
    params: &FilterParams,
    prev_cmd: &Control,
    current_vel: f64,
    dt: f64,
) {
    let lim = interpolate_from_speed(
        &params.lon_jerk_lim_for_lon_acc,
        &params.reference_speed_points,
        current_vel,
    );
    cmd.longitudinal.acceleration = limit_diff(
        cmd.longitudinal.acceleration,
        prev_cmd.longitudinal.acceleration,
        lim * dt,
    );
    cmd.longitudinal.jerk = cmd.longitudinal.jerk.max(-lim).min(lim);
}

/// Clamp acceleration and limit velocity change by acc × dt.
fn limit_longitudinal_with_acc(
    cmd: &mut Control,
    params: &FilterParams,
    prev_cmd: &Control,
    current_vel: f64,
    dt: f64,
) {
    let lim = interpolate_from_speed(
        &params.lon_acc_lim_for_lon_vel,
        &params.reference_speed_points,
        current_vel,
    );
    cmd.longitudinal.acceleration =
        cmd.longitudinal.acceleration.max(-lim).min(lim);
    cmd.longitudinal.velocity = limit_diff(
        cmd.longitudinal.velocity,
        prev_cmd.longitudinal.velocity,
        lim * dt,
    );
}

/// Clamp velocity to ±vel_lim.
fn limit_longitudinal_with_vel(cmd: &mut Control, params: &FilterParams) {
    cmd.longitudinal.velocity = cmd
        .longitudinal
        .velocity
        .max(-params.vel_lim)
        .min(params.vel_lim);
}

/// Limit steering so that lateral jerk (change in lateral acceleration) stays within bounds.
/// Uses actual ego speed (not command speed) to avoid oscillation when command velocity oscillates.
fn limit_lateral_with_lat_jerk(
    cmd: &mut Control,
    params: &FilterParams,
    prev_cmd: &Control,
    current_vel: f64,
    dt: f64,
) {
    let lim = interpolate_from_speed(
        &params.lat_jerk_lim_for_steer_cmd,
        &params.reference_speed_points,
        current_vel,
    );
    let curr_latacc =
        calc_lat_acc(cmd.lateral.steering_tire_angle, current_vel, params.wheel_base);
    let prev_latacc =
        calc_lat_acc(prev_cmd.lateral.steering_tire_angle, current_vel, params.wheel_base);
    let latacc_max = prev_latacc + lim * dt;
    let latacc_min = prev_latacc - lim * dt;
    if curr_latacc > latacc_max {
        cmd.lateral.steering_tire_angle =
            calc_steer_from_latacc(current_vel, latacc_max, params.wheel_base);
    } else if curr_latacc < latacc_min {
        cmd.lateral.steering_tire_angle =
            calc_steer_from_latacc(current_vel, latacc_min, params.wheel_base);
    }
}

/// Clamp steering so that lateral acceleration stays within bounds.
/// Uses actual ego speed (not command speed) — same rationale as limit_lateral_with_lat_jerk.
fn limit_lateral_with_lat_acc(cmd: &mut Control, params: &FilterParams, current_vel: f64) {
    let lim = interpolate_from_speed(
        &params.lat_acc_lim_for_steer_cmd,
        &params.reference_speed_points,
        current_vel,
    );
    let latacc = calc_lat_acc(cmd.lateral.steering_tire_angle, current_vel, params.wheel_base);
    if libm::fabs(latacc) > lim {
        let v_sq = (current_vel * current_vel).max(0.001);
        let steer_lim = libm::atan(lim * params.wheel_base / v_sq);
        cmd.lateral.steering_tire_angle = if latacc > 0.0 { steer_lim } else { -steer_lim };
    }
}

/// Clamp how far the steering command can differ from the current actual steer angle.
fn limit_actual_steer_diff(
    cmd: &mut Control,
    params: &FilterParams,
    current_vel: f64,
    current_steer: f64,
) {
    let lim = interpolate_from_speed(
        &params.steer_cmd_diff_lim_from_current_steer,
        &params.reference_speed_points,
        current_vel,
    );
    let ds = (cmd.lateral.steering_tire_angle - current_steer)
        .max(-lim)
        .min(lim);
    cmd.lateral.steering_tire_angle = current_steer + ds;
}
