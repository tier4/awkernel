// Copyright 2022 Autoware Foundation
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
// original file path: localization/autoware_ekf_localizer/src/state_transition.cpp
// test code: localization/autoware_ekf_localizer/test/test_state_transition.cpp
// version: 1.8.0

use libm::{atan2, cos, sin};

use crate::{StateCovariance, StateIndex, StateVector};

pub fn normalize_yaw(yaw: f64) -> f64 {
    atan2(sin(yaw), cos(yaw))
}

/*  == Nonlinear model ==
 *
 * x_{k+1}   = x_k + vx_k * cos(yaw_k + b_k) * dt
 * y_{k+1}   = y_k + vx_k * sin(yaw_k + b_k) * dt
 * yaw_{k+1} = yaw_k + (wz_k) * dt
 * b_{k+1}   = b_k
 * vx_{k+1}  = vx_k
 * wz_{k+1}  = wz_k
 *
 * (b_k : yaw_bias_k)
 */
pub fn predict_next_state(x_curr: &StateVector, dt: f64) -> StateVector {
    let x = x_curr[StateIndex::X as usize];
    let y = x_curr[StateIndex::Y as usize];
    let yaw = x_curr[StateIndex::Yaw as usize];
    let yaw_bias = x_curr[StateIndex::YawBias as usize];
    let vx = x_curr[StateIndex::Vx as usize];
    let wz = x_curr[StateIndex::Wz as usize];

    let mut x_next = *x_curr;
    x_next[StateIndex::X as usize] = x + vx * cos(yaw + yaw_bias) * dt;
    x_next[StateIndex::Y as usize] = y + vx * sin(yaw + yaw_bias) * dt;
    x_next[StateIndex::Yaw as usize] = normalize_yaw(yaw + wz * dt);
    x_next[StateIndex::YawBias as usize] = yaw_bias;
    x_next[StateIndex::Vx as usize] = vx;
    x_next[StateIndex::Wz as usize] = wz;
    x_next
}

/*  == Linearized model ==
 *
 * A = [ 1, 0, -vx*sin(yaw+b)*dt, -vx*sin(yaw+b)*dt, cos(yaw+b)*dt,  0]
 *     [ 0, 1,  vx*cos(yaw+b)*dt,  vx*cos(yaw+b)*dt, sin(yaw+b)*dt,  0]
 *     [ 0, 0,                 1,                 0,             0, dt]
 *     [ 0, 0,                 0,                 1,             0,  0]
 *     [ 0, 0,                 0,                 0,             1,  0]
 *     [ 0, 0,                 0,                 0,             0,  1]
 */
pub fn create_state_transition_matrix(x_curr: &StateVector, dt: f64) -> StateCovariance {
    let yaw = x_curr[StateIndex::Yaw as usize];
    let yaw_bias = x_curr[StateIndex::YawBias as usize];
    let vx = x_curr[StateIndex::Vx as usize];

    let mut a = StateCovariance::identity();
    a[(StateIndex::X as usize, StateIndex::Yaw as usize)] = -vx * sin(yaw + yaw_bias) * dt;
    a[(StateIndex::X as usize, StateIndex::YawBias as usize)] = -vx * sin(yaw + yaw_bias) * dt;
    a[(StateIndex::X as usize, StateIndex::Vx as usize)] = cos(yaw + yaw_bias) * dt;
    a[(StateIndex::Y as usize, StateIndex::Yaw as usize)] = vx * cos(yaw + yaw_bias) * dt;
    a[(StateIndex::Y as usize, StateIndex::YawBias as usize)] = vx * cos(yaw + yaw_bias) * dt;
    a[(StateIndex::Y as usize, StateIndex::Vx as usize)] = sin(yaw + yaw_bias) * dt;
    a[(StateIndex::Yaw as usize, StateIndex::Wz as usize)] = dt;
    a
}

pub fn process_noise_covariance(
    proc_cov_yaw_d: f64,
    proc_cov_vx_d: f64,
    proc_cov_wz_d: f64,
) -> StateCovariance {
    let mut q = StateCovariance::zeros();
    q[(StateIndex::Yaw as usize, StateIndex::Yaw as usize)] = proc_cov_yaw_d;
    q[(StateIndex::Vx as usize, StateIndex::Vx as usize)] = proc_cov_vx_d;
    q[(StateIndex::Wz as usize, StateIndex::Wz as usize)] = proc_cov_wz_d;
    q
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::f64::consts::PI;
    use libm::sqrt;
    use nalgebra::Vector6;

    // Expected values are computed via the same `libm` free functions `predict_next_state`
    // itself uses (`cos`/`sin`/`atan2`, imported above through `use super::*`), not `f64`'s
    // std-backed `.cos()/.sin()/.atan2()` methods. Those std methods resolve here too --
    // `cargo test` links `std` for the test harness even though this crate is `#![no_std]`
    // -- but doing so would silently compare this crate's `libm` output against the host's
    // glibc `libm.so` (confirmed via `nm -D`/`ldd` on the test binary: it pulls in
    // `cos@GLIBC`/`sin@GLIBC`/`atan2@GLIBC`), two independent implementations that are not
    // guaranteed to agree bit-for-bit. Using the same implementation on both sides, like
    // upstream does (its test reuses its own `normalize_yaw` for the expected yaw), lets
    // every component share the same tight 1e-10 tolerance instead of loosening yaw's.
    #[test]
    fn predict_next_state_matches_formula() {
        let x_curr = Vector6::new(2.0, 3.0, PI / 2.0, PI / 4.0, 10.0, 2.0 * PI / 3.0);
        let dt = 0.5;
        let x_next = predict_next_state(&x_curr, dt);

        let tol = 1e-10;
        assert!((x_next[0] - (2.0 + 10.0 * cos(PI / 2.0 + PI / 4.0) * dt)).abs() < tol);
        assert!((x_next[1] - (3.0 + 10.0 * sin(PI / 2.0 + PI / 4.0) * dt)).abs() < tol);
        let yaw_next = PI / 2.0 + (2.0 * PI / 3.0) * dt;
        let expected_yaw = atan2(sin(yaw_next), cos(yaw_next));
        assert!((x_next[2] - expected_yaw).abs() < tol);
        assert!((x_next[3] - x_curr[3]).abs() < tol);
        assert!((x_next[4] - x_curr[4]).abs() < tol);
        assert!((x_next[5] - x_curr[5]).abs() < tol);
    }

    // Matches upstream test_state_transition.cpp's
    // `create_state_transition_matrix.NumericalApproximation` exactly, including its
    // per-case tolerance (2e-3 around x=0, 5e-3 around the non-zero x): a single shared
    // tolerance would be looser than upstream for the x=0 case.
    #[test]
    fn create_state_transition_matrix_numeric_approximation() {
        let dt = 0.1;
        let dx = Vector6::from_element(0.1);

        for (x, tolerance) in [
            (Vector6::zeros(), 2e-3),
            (Vector6::new(0.1, 0.2, 0.1, 0.4, 0.1, 0.3), 5e-3),
        ] {
            let a = create_state_transition_matrix(&x, dt);
            let x1 = predict_next_state(&(x + dx), dt);
            let x0 = predict_next_state(&x, dt);
            let df = x1 - x0;

            let v = df - a * dx;
            let mut s = 0.0;
            for i in 0..6 {
                s += v[i] * v[i];
            }
            assert!(sqrt(s) < tolerance);
        }
    }

    // Matches upstream's `process_noise_covariance.process_noise_covariance` exactly:
    // `process_noise_covariance(1., 2., 3.)`. The function already takes pre-computed
    // proc_cov_*_d (variance-level) values, not stddevs to be squared, so the arguments
    // are used as-is -- squaring them here would misleadingly imply a squaring step that
    // doesn't belong in this test.
    #[test]
    fn process_noise_covariance_values() {
        let q = process_noise_covariance(1.0, 2.0, 3.0);

        // indices: yaw = 2, vx = 4, wz = 5
        assert_eq!(q[(2, 2)], 1.0);
        assert_eq!(q[(4, 4)], 2.0);
        assert_eq!(q[(5, 5)], 3.0);

        let q2 = process_noise_covariance(0.0, 0.0, 0.0);
        let mut s = 0.0;
        for i in 0..6 {
            for j in 0..6 {
                let val = q2[(i, j)];
                s += val * val;
            }
        }
        assert_eq!(s, 0.0);
    }

    #[test]
    fn normalize_yaw_wraps_into_pi_range() {
        let tol = 1e-6;
        // Exact fixtures from upstream test_state_transition.cpp's `StateTransition.normalize_yaw`.
        assert!((normalize_yaw(PI * 4.0 / 3.0) - (-PI * 2.0 / 3.0)).abs() < tol);
        assert!((normalize_yaw(-PI * 4.0 / 3.0) - (PI * 2.0 / 3.0)).abs() < tol);
        assert!((normalize_yaw(PI * 9.0 / 2.0) - (PI * 1.0 / 2.0)).abs() < tol);
        assert!((normalize_yaw(PI * 4.0) - 0.0).abs() < tol);

        // [own additions] no upstream equivalent below; covers the trivial 0 input and
        // the exact-π boundary (where atan2's branch cut sits), neither of which
        // upstream's four fixtures above happen to land on.
        let tol_tight = 1e-9;
        assert!((normalize_yaw(0.0) - 0.0).abs() < tol_tight);
        assert!((normalize_yaw(2.0 * PI) - 0.0).abs() < tol_tight);
        assert!((normalize_yaw(PI + 0.1) - (-PI + 0.1)).abs() < tol);
    }
}
