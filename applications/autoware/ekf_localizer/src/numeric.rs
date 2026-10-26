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
// original file path: localization/autoware_ekf_localizer/src/include/numeric.hpp
// test code: localization/autoware_ekf_localizer/test/test_numeric.cpp
// version: 1.8.0
//
// Kept as its own module, matching upstream's `numeric.hpp` file boundary, so
// `test_numeric.cpp`'s exact fixtures can be ported as real unit tests instead of only
// being exercised indirectly through `EKFModule` integration tests.

use nalgebra::DVector;

pub fn has_nan(v: &DVector<f64>) -> bool {
    v.iter().any(|x| x.is_nan())
}

pub fn has_inf(v: &DVector<f64>) -> bool {
    v.iter().any(|x| x.is_infinite())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn has_nan_detects_nan_but_not_inf_or_large_finite_values() {
        let empty = DVector::from_vec(alloc::vec![]);
        let inf = f64::INFINITY;
        let nan = f64::NAN;

        assert!(!has_nan(&empty));
        assert!(!has_nan(&DVector::from_vec(alloc::vec![0.0, 0.0, 1.0])));
        assert!(!has_nan(&DVector::from_vec(alloc::vec![1e16, 0.0, 1.0])));
        assert!(!has_nan(&DVector::from_vec(alloc::vec![0.0, 1.0, inf])));

        assert!(has_nan(&DVector::from_vec(alloc::vec![nan, 1.0, 0.0])));
    }

    #[test]
    fn has_inf_detects_inf_but_not_nan_or_large_finite_values() {
        let empty = DVector::from_vec(alloc::vec![]);
        let inf = f64::INFINITY;
        let nan = f64::NAN;

        assert!(!has_inf(&empty));
        assert!(!has_inf(&DVector::from_vec(alloc::vec![0.0, 0.0, 1.0])));
        assert!(!has_inf(&DVector::from_vec(alloc::vec![1e16, 0.0, 1.0])));
        assert!(!has_inf(&DVector::from_vec(alloc::vec![nan, 1.0, 0.0])));

        assert!(has_inf(&DVector::from_vec(alloc::vec![0.0, 1.0, inf])));
    }
}
