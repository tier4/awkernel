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
// original file path: localization/autoware_ekf_localizer/src/measurement.cpp
// test code: localization/autoware_ekf_localizer/test/test_measurement.cpp
// version: 1.8.0

use nalgebra::DMatrix;

use crate::StateIndex;

// Every function below returns `DMatrix<f64>` even though its shape (3x6, 2x6, 3x3, 2x2)
// is fixed and known here -- a fixed-size nalgebra type (`Matrix3<f64>`, etc., mirroring
// upstream's `Eigen::Matrix3d`) would type-check just as well locally. `DMatrix` is used
// instead so the result can be passed directly as the `c`/`r` argument of
// `kalman_filter::DelayCompensatedKalmanFilter::update_with_delay`, which is itself
// `DMatrix`-typed because *its* dimensions (`dim_x_ex = dim_x * max_delay_step`) are only
// known at runtime. See kalman_filter.rs for that constraint.

// XYZRPY (6x6, row-major) covariance array indices, matching
// autoware_utils_geometry::xyzrpy_covariance_index::XYZRPY_COV_IDX used upstream.
const X_X: usize = 0;
const X_Y: usize = 1;
const X_YAW: usize = 5;
const Y_X: usize = 6;
const Y_Y: usize = 7;
const Y_YAW: usize = 11;
const YAW_X: usize = 30;
const YAW_Y: usize = 31;
const YAW_YAW: usize = 35;

pub fn pose_measurement_matrix() -> DMatrix<f64> {
    let mut c = DMatrix::zeros(3, 6);
    c[(0, StateIndex::X as usize)] = 1.0;
    c[(1, StateIndex::Y as usize)] = 1.0;
    c[(2, StateIndex::Yaw as usize)] = 1.0;
    c
}

pub fn twist_measurement_matrix() -> DMatrix<f64> {
    let mut c = DMatrix::zeros(2, 6);
    c[(0, StateIndex::Vx as usize)] = 1.0;
    c[(1, StateIndex::Wz as usize)] = 1.0;
    c
}

pub fn pose_measurement_covariance(covariance: &[f64; 36], smoothing_step: usize) -> DMatrix<f64> {
    let mut r = DMatrix::zeros(3, 3);
    r[(0, 0)] = covariance[X_X];
    r[(0, 1)] = covariance[X_Y];
    r[(0, 2)] = covariance[X_YAW];
    r[(1, 0)] = covariance[Y_X];
    r[(1, 1)] = covariance[Y_Y];
    r[(1, 2)] = covariance[Y_YAW];
    r[(2, 0)] = covariance[YAW_X];
    r[(2, 1)] = covariance[YAW_Y];
    r[(2, 2)] = covariance[YAW_YAW];
    r * smoothing_step as f64
}

pub fn twist_measurement_covariance(covariance: &[f64; 36], smoothing_step: usize) -> DMatrix<f64> {
    let mut r = DMatrix::zeros(2, 2);
    r[(0, 0)] = covariance[X_X];
    r[(0, 1)] = covariance[X_YAW];
    r[(1, 0)] = covariance[YAW_X];
    r[(1, 1)] = covariance[YAW_YAW];
    r * smoothing_step as f64
}

#[cfg(test)]
mod tests {
    use super::*;

    // Matches upstream test_measurement.cpp's `Measurement.pose_measurement_matrix`
    // fixture (`expected << 1,0,0,0,0,0, 0,1,0,0,0,0, 0,0,1,0,0,0;`), checked element-wise
    // (including every entry that should be zero) instead of building the full expected
    // matrix and comparing norms, since this crate doesn't need an Eigen-style matrix
    // literal builder for a one-off test.
    #[test]
    fn pose_measurement_matrix_picks_x_y_yaw() {
        let c = pose_measurement_matrix();
        assert_eq!(c.shape(), (3, 6));
        for i in 0..3 {
            for j in 0..6 {
                let expected = if (i, j) == (0, StateIndex::X as usize)
                    || (i, j) == (1, StateIndex::Y as usize)
                    || (i, j) == (2, StateIndex::Yaw as usize)
                {
                    1.0
                } else {
                    0.0
                };
                assert_eq!(c[(i, j)], expected, "mismatch at ({i},{j})");
            }
        }
    }

    // Matches upstream's `Measurement.twist_measurement_matrix`
    // (`expected << 0,0,0,0,1,0, 0,0,0,0,0,1;`).
    #[test]
    fn twist_measurement_matrix_picks_vx_wz() {
        let c = twist_measurement_matrix();
        assert_eq!(c.shape(), (2, 6));
        for i in 0..2 {
            for j in 0..6 {
                let expected = if (i, j) == (0, StateIndex::Vx as usize)
                    || (i, j) == (1, StateIndex::Wz as usize)
                {
                    1.0
                } else {
                    0.0
                };
                assert_eq!(c[(i, j)], expected, "mismatch at ({i},{j})");
            }
        }
    }

    // Matches upstream's `Measurement.pose_measurement_covariance` exactly (same
    // covariance array fixture and smoothing_step=2, same expected 3x3), including the
    // off-diagonal cross-terms (X_Y, X_YAW, Y_X, Y_YAW, YAW_X, YAW_Y). A diagonal-only
    // check cannot catch a transposition bug (e.g. reading Y_X into the X_Y slot), since
    // that would still leave every diagonal entry correct.
    #[test]
    fn pose_measurement_covariance_preserves_cross_terms_and_scales_by_smoothing_step() {
        let mut cov = [0.0; 36];
        cov[X_X] = 1.0;
        cov[X_Y] = 2.0;
        cov[X_YAW] = 3.0;
        cov[Y_X] = 4.0;
        cov[Y_Y] = 5.0;
        cov[Y_YAW] = 6.0;
        cov[YAW_X] = 7.0;
        cov[YAW_Y] = 8.0;
        cov[YAW_YAW] = 9.0;

        let r = pose_measurement_covariance(&cov, 2);
        let expected = [[2.0, 4.0, 6.0], [8.0, 10.0, 12.0], [14.0, 16.0, 18.0]];
        for i in 0..3 {
            for j in 0..3 {
                assert_eq!(r[(i, j)], expected[i][j], "mismatch at ({i},{j})");
            }
        }
    }

    // Matches upstream's "make sure that other elements are not changed" sub-case.
    #[test]
    fn pose_measurement_covariance_zero_input_yields_zero_output() {
        let cov = [0.0; 36];
        let r = pose_measurement_covariance(&cov, 2);
        assert_eq!(r.iter().map(|v| v * v).sum::<f64>(), 0.0);
    }

    // Matches upstream's `Measurement.twist_measurement_covariance` exactly, including
    // the X_YAW/YAW_X off-diagonal terms (deliberately given different values, 2 vs 3, so
    // a transposition bug would be caught).
    //
    // Omits upstream's extra `covariance[11] = 6` (Y_YAW, a slot this function never
    // reads): an unset (zero) slot there still gets caught by the assertion below if it
    // were accidentally read, so a non-zero noise value isn't needed to detect that bug
    // class.
    #[test]
    fn twist_measurement_covariance_preserves_cross_terms_and_scales_by_smoothing_step() {
        let mut cov = [0.0; 36];
        cov[X_X] = 1.0;
        cov[X_YAW] = 2.0;
        cov[YAW_X] = 3.0;
        cov[YAW_YAW] = 4.0;

        let r = twist_measurement_covariance(&cov, 2);
        let expected = [[2.0, 4.0], [6.0, 8.0]];
        for i in 0..2 {
            for j in 0..2 {
                assert_eq!(r[(i, j)], expected[i][j], "mismatch at ({i},{j})");
            }
        }
    }

    #[test]
    fn twist_measurement_covariance_zero_input_yields_zero_output() {
        let cov = [0.0; 36];
        let r = twist_measurement_covariance(&cov, 2);
        assert_eq!(r.iter().map(|v| v * v).sum::<f64>(), 0.0);
    }
}
