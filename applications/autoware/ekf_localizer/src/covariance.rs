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
// original file path: localization/autoware_ekf_localizer/src/covariance.cpp
// test code: localization/autoware_ekf_localizer/test/test_covariance.cpp
// version: 1.8.0

use nalgebra::DMatrix;

use crate::StateIndex;

// XYZRPY (6x6, row-major) covariance array indices, same layout as measurement.rs.
// Only the 9 entries this file's two functions actually use are pulled out of upstream's
// XYZRPY_COV_IDX enum (which defines all 36: X_Z, X_ROLL, Z_Z, ROLL_ROLL, PITCH_PITCH,
// etc. are defined there but unused here) -- not an incomplete port.
const X_X: usize = 0;
const X_Y: usize = 1;
const X_YAW: usize = 5;
const Y_X: usize = 6;
const Y_Y: usize = 7;
const Y_YAW: usize = 11;
const YAW_X: usize = 30;
const YAW_Y: usize = 31;
const YAW_YAW: usize = 35;

/// Converts the 6x6 EKF state covariance into a ROS-style 6x6 (XYZRPY) flattened
/// pose covariance, filling in only the X/Y/YAW block (Z/ROLL/PITCH come from the
/// Simple1DFilters and are overwritten by the caller).
pub fn ekf_covariance_to_pose_message_covariance(p: &DMatrix<f64>) -> [f64; 36] {
    let x = StateIndex::X as usize;
    let y = StateIndex::Y as usize;
    let yaw = StateIndex::Yaw as usize;

    let mut covariance = [0.0; 36];
    covariance[X_X] = p[(x, x)];
    covariance[X_Y] = p[(x, y)];
    covariance[X_YAW] = p[(x, yaw)];
    covariance[Y_X] = p[(y, x)];
    covariance[Y_Y] = p[(y, y)];
    covariance[Y_YAW] = p[(y, yaw)];
    covariance[YAW_X] = p[(yaw, x)];
    covariance[YAW_Y] = p[(yaw, y)];
    covariance[YAW_YAW] = p[(yaw, yaw)];
    covariance
}

/// Converts the 6x6 EKF state covariance into a ROS-style flattened twist covariance,
/// mapping VX -> linear.x and WZ -> angular.z.
pub fn ekf_covariance_to_twist_message_covariance(p: &DMatrix<f64>) -> [f64; 36] {
    let vx = StateIndex::Vx as usize;
    let wz = StateIndex::Wz as usize;

    let mut covariance = [0.0; 36];
    covariance[X_X] = p[(vx, vx)];
    covariance[X_YAW] = p[(vx, wz)];
    covariance[YAW_X] = p[(wz, vx)];
    covariance[YAW_YAW] = p[(wz, wz)];
    covariance
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pose_covariance_mapping() {
        let mut p = DMatrix::<f64>::zeros(6, 6);
        p[(0, 0)] = 1.0;
        p[(0, 1)] = 2.0;
        p[(0, 2)] = 3.0;
        p[(1, 0)] = 4.0;
        p[(1, 1)] = 5.0;
        p[(1, 2)] = 6.0;
        p[(2, 0)] = 7.0;
        p[(2, 1)] = 8.0;
        p[(2, 2)] = 9.0;

        let cov = ekf_covariance_to_pose_message_covariance(&p);
        assert_eq!(cov[0], 1.0);
        assert_eq!(cov[1], 2.0);
        assert_eq!(cov[5], 3.0);
        assert_eq!(cov[6], 4.0);
        assert_eq!(cov[7], 5.0);
        assert_eq!(cov[11], 6.0);
        assert_eq!(cov[30], 7.0);
        assert_eq!(cov[31], 8.0);
        assert_eq!(cov[35], 9.0);
    }

    // Matches upstream test_covariance.cpp's "ensure other elements are zero" sub-case:
    // with an all-zero input, every one of the 36 output slots (not just the 9 mapped
    // ones) must be zero -- catches accidental garbage/uninitialized values in the
    // unmapped Z/ROLL/PITCH slots this function doesn't touch.
    #[test]
    fn pose_covariance_mapping_zero_input_yields_zero_output() {
        let p = DMatrix::<f64>::zeros(6, 6);
        let cov = ekf_covariance_to_pose_message_covariance(&p);
        for e in cov {
            assert_eq!(e, 0.0);
        }
    }

    // Matches upstream's `EKFCovarianceToTwistMessageCovariance.SmokeTest` exactly,
    // including the X_YAW/YAW_X off-diagonal terms (deliberately given different values,
    // 2 vs 3, so a transposition bug would be caught).
    #[test]
    fn twist_covariance_mapping() {
        let mut p = DMatrix::<f64>::zeros(6, 6);
        p[(4, 4)] = 1.0;
        p[(4, 5)] = 2.0;
        p[(5, 4)] = 3.0;
        p[(5, 5)] = 4.0;

        let cov = ekf_covariance_to_twist_message_covariance(&p);
        assert_eq!(cov[0], 1.0);
        assert_eq!(cov[5], 2.0);
        assert_eq!(cov[30], 3.0);
        assert_eq!(cov[35], 4.0);
    }

    // Matches upstream's "ensure other elements are zero" sub-case for the twist mapping.
    #[test]
    fn twist_covariance_mapping_zero_input_yields_zero_output() {
        let p = DMatrix::<f64>::zeros(6, 6);
        let cov = ekf_covariance_to_twist_message_covariance(&p);
        for e in cov {
            assert_eq!(e, 0.0);
        }
    }
}
