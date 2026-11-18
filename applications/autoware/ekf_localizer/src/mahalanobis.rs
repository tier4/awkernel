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
// original file path: localization/autoware_ekf_localizer/src/mahalanobis.cpp
// test code: localization/autoware_ekf_localizer/test/test_mahalanobis.cpp
// version: 1.8.0

use libm::sqrt;
use nalgebra::{DMatrix, DVector};

/// Squared Mahalanobis distance between `x` and `y` under covariance `c`.
///
/// NOTE: upstream calls `C.inverse()` unconditionally (Eigen does not check
/// invertibility). Here a singular `C` is treated as "infinitely far apart" so that
/// callers gating on a distance threshold reject the measurement instead of dividing
/// by a garbage value.
pub fn squared_mahalanobis(x: &DVector<f64>, y: &DVector<f64>, c: &DMatrix<f64>) -> f64 {
    let d = x - y;
    match c.clone().try_inverse() {
        Some(c_inv) => d.dot(&(c_inv * &d)),
        None => f64::INFINITY,
    }
}

pub fn mahalanobis(x: &DVector<f64>, y: &DVector<f64>, c: &DMatrix<f64>) -> f64 {
    sqrt(squared_mahalanobis(x, y, c))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Exact fixtures from upstream test_mahalanobis.cpp's `squared_mahalanobis.SmokeTest`
    // (x=(0,1), y=(3,2), c=diag(10,10) -> 1.0; x=(4,1), y=(1,5), c=diag(5,5) -> 5.0).
    #[test]
    fn squared_mahalanobis_matches_hand_computed_values_for_diagonal_covariance() {
        let c1 = DMatrix::from_diagonal(&DVector::from_vec(alloc::vec![10.0, 10.0]));
        let x1 = DVector::from_vec(alloc::vec![0.0, 1.0]);
        let y1 = DVector::from_vec(alloc::vec![3.0, 2.0]);
        assert!((squared_mahalanobis(&x1, &y1, &c1) - 1.0).abs() <= 1e-8);

        let c2 = DMatrix::from_diagonal(&DVector::from_vec(alloc::vec![5.0, 5.0]));
        let x2 = DVector::from_vec(alloc::vec![4.0, 1.0]);
        let y2 = DVector::from_vec(alloc::vec![1.0, 5.0]);
        assert!((squared_mahalanobis(&x2, &y2, &c2) - 5.0).abs() <= 1e-8);
    }

    // Exact fixtures from upstream's `mahalanobis.SmokeTest` (same two cases as above,
    // through the sqrt-wrapping `mahalanobis` function).
    #[test]
    fn mahalanobis_matches_hand_computed_values_for_diagonal_covariance() {
        let c1 = DMatrix::from_diagonal(&DVector::from_vec(alloc::vec![10.0, 10.0]));
        let x1 = DVector::from_vec(alloc::vec![0.0, 1.0]);
        let y1 = DVector::from_vec(alloc::vec![3.0, 2.0]);
        assert!((mahalanobis(&x1, &y1, &c1) - 1.0).abs() <= 1e-8);

        let c2 = DMatrix::from_diagonal(&DVector::from_vec(alloc::vec![5.0, 5.0]));
        let x2 = DVector::from_vec(alloc::vec![4.0, 1.0]);
        let y2 = DVector::from_vec(alloc::vec![1.0, 5.0]);
        assert!((mahalanobis(&x2, &y2, &c2) - sqrt(5.0)).abs() <= 1e-8);
    }

    // [own test] no upstream equivalent; covers the x==y degenerate case (distance must
    // be exactly 0, not just "small"), which neither upstream fixture happens to exercise.
    #[test]
    fn zero_distance_when_points_match() {
        let x = DVector::from_vec(alloc::vec![1.0, 2.0]);
        let y = x.clone();
        let c = DMatrix::<f64>::identity(2, 2);
        assert_eq!(mahalanobis(&x, &y, &c), 0.0);
    }

    // [own test] no upstream equivalent; pins down the specific "identity covariance
    // reduces to plain Euclidean distance" interpretation using a well-known 3-4-5
    // triangle, which is easier to sanity-check by eye than upstream's
    // diag(10,10)/diag(5,5) fixtures.
    #[test]
    fn identity_covariance_is_euclidean_distance() {
        let x = DVector::from_vec(alloc::vec![3.0, 0.0]);
        let y = DVector::from_vec(alloc::vec![0.0, 4.0]);
        let c = DMatrix::<f64>::identity(2, 2);
        assert!((mahalanobis(&x, &y, &c) - 5.0).abs() < 1e-12);
    }

    // [own test] no upstream equivalent; verifies the monotonic direction (looser
    // covariance -> smaller distance) that upstream's two independent point fixtures
    // don't directly compare against each other.
    #[test]
    fn larger_variance_shrinks_the_distance() {
        let x = DVector::from_vec(alloc::vec![2.0]);
        let y = DVector::from_vec(alloc::vec![0.0]);
        let tight = DMatrix::from_element(1, 1, 1.0);
        let loose = DMatrix::from_element(1, 1, 100.0);
        assert!(mahalanobis(&x, &y, &loose) < mahalanobis(&x, &y, &tight));
    }

    // [own test] no upstream equivalent (Eigen's `.inverse()` on a singular matrix
    // silently returns garbage rather than erroring); locks in this crate's deliberate
    // divergence -- see the NOTE on `squared_mahalanobis` above -- of treating a singular
    // covariance as "infinitely far" instead.
    #[test]
    fn singular_covariance_is_treated_as_infinitely_far() {
        let x = DVector::from_vec(alloc::vec![1.0, 0.0]);
        let y = DVector::from_vec(alloc::vec![0.0, 0.0]);
        let c = DMatrix::<f64>::zeros(2, 2);
        assert!(mahalanobis(&x, &y, &c).is_infinite());
    }
}
