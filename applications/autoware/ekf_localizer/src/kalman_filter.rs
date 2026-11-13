// Copyright 2018-2019 Autoware Foundation
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
// original file path: common/autoware_kalman_filter/{include/autoware/kalman_filter/time_delay_kalman_filter.hpp, src/time_delay_kalman_filter.cpp}
// test code: common/autoware_kalman_filter/test/test_time_delay_kalman_filter.cpp
// version: 1.8.0
//
// NOTE: this is not part of the autoware_ekf_localizer package upstream. It is a shared
// Autoware utility (`autoware_kalman_filter`) that `ekf_module.cpp` depends on via
// `#include <autoware/kalman_filter/time_delay_kalman_filter.hpp>`. It is ported here,
// scoped to this crate, because no standalone kalman_filter crate exists in this
// repository yet.
//
// RT NOTE: `predict_with_delay`/`update_with_delay` run on the EKF's periodic predict/update
// tick, so they are treated as RT-critical. Every buffer they touch is preallocated once in
// `init()`; the two methods only read/write into those buffers (via `copy_from`/`gemm`/
// `mul_to`, and a small number of fixed-bound element-wise loops) instead of calling
// `DMatrix::zeros`/`.clone_owned()` on every call. See each method's WCET contract for the
// one remaining bounded exception.

extern crate alloc;

use nalgebra::{DMatrix, DVector};

/// Upper bound on `max_delay_step` (i.e. upstream's `extend_state_step`) accepted by
/// `init`. This bounds the O(dim_x^2 * max_delay_step^2) memory used by `p_ex` and its
/// scratch buffers so a misconfigured caller cannot silently blow up allocation size at
/// `init()` time. Upstream's own shipped default is 50; 200 leaves generous headroom
/// while still being a fixed, documented cap.
pub const MAX_DELAY_STEP: usize = 200;

/// Upper bound on the measurement dimension (`dim_y`) accepted by `update_with_delay`.
/// Fixing this bound lets `update_with_delay`'s scratch buffers (`e`, `c_transpose`,
/// `c_p_dd`, `s`, `p_ct`, `k_transpose`, `k`) be sized once in `init()` instead of
/// reallocating on every call. This crate's only two callers use `dim_y = 3` (pose: x,
/// y, yaw) and `dim_y = 2` (twist: vx, wz), so 3 covers both with no slack to spare for
/// a third caller — bump this (and re-check the scratch buffer sizes below) before
/// adding one.
const MAX_DIM_Y: usize = 3;

/// Kalman filter that keeps an extended state history so that measurements which arrive
/// with a known delay can be fused against the state as it was `delay_step` predict-ticks
/// ago, instead of being (incorrectly) fused against the *current* state.
///
/// All scratch buffers used by `predict_with_delay`/`update_with_delay` are preallocated
/// by `init()`; see the WCET contract on each method.
#[derive(Debug, Clone)]
pub struct DelayCompensatedKalmanFilter {
    dim_x: usize,
    max_delay_step: usize,
    x_ex: DVector<f64>,
    p_ex: DMatrix<f64>,

    // --- predict_with_delay scratch (sized in `init()`) ---
    x_next_ex: DVector<f64>,   // dim_x_ex
    p_next_ex: DMatrix<f64>,   // dim_x_ex x dim_x_ex; also reused by update_with_delay
    a_transpose: DMatrix<f64>, // dim_x x dim_x
    ap11: DMatrix<f64>,        // dim_x x dim_x

    // --- update_with_delay scratch (sized in `init()`) ---
    x_d: DVector<f64>,         // dim_x
    e: DVector<f64>,           // MAX_DIM_Y, use rows(0, dim_y)
    c_transpose: DMatrix<f64>, // dim_x x MAX_DIM_Y
    c_p_dd: DMatrix<f64>,      // MAX_DIM_Y x dim_x
    s: DMatrix<f64>,           // MAX_DIM_Y x MAX_DIM_Y
    p_ct: DMatrix<f64>,        // dim_x_ex x MAX_DIM_Y
    k_transpose: DMatrix<f64>, // MAX_DIM_Y x dim_x_ex
    k: DMatrix<f64>,           // dim_x_ex x MAX_DIM_Y
}

impl DelayCompensatedKalmanFilter {
    pub fn new() -> Self {
        Self {
            dim_x: 0,
            max_delay_step: 0,
            x_ex: DVector::zeros(0),
            p_ex: DMatrix::zeros(0, 0),
            x_next_ex: DVector::zeros(0),
            p_next_ex: DMatrix::zeros(0, 0),
            a_transpose: DMatrix::zeros(0, 0),
            ap11: DMatrix::zeros(0, 0),
            x_d: DVector::zeros(0),
            e: DVector::zeros(MAX_DIM_Y),
            c_transpose: DMatrix::zeros(0, MAX_DIM_Y),
            c_p_dd: DMatrix::zeros(MAX_DIM_Y, 0),
            s: DMatrix::zeros(MAX_DIM_Y, MAX_DIM_Y),
            p_ct: DMatrix::zeros(0, MAX_DIM_Y),
            k_transpose: DMatrix::zeros(MAX_DIM_Y, 0),
            k: DMatrix::zeros(0, MAX_DIM_Y),
        }
    }

    /// Initializes (or re-initializes) the filter and (re)allocates every scratch buffer
    /// used by `predict_with_delay`/`update_with_delay`. This is a setup-phase operation
    /// (called at construction, and again on a re-localization event) — allocation here is
    /// expected and fine; it is the *only* place in this type that allocates.
    ///
    /// `max_delay_step` is clamped to `MAX_DELAY_STEP` (logged as an error if it was over
    /// the cap) so a misconfigured caller cannot make every later `predict_with_delay` call
    /// allocate-free but arbitrarily large.
    pub fn init(&mut self, x: &DVector<f64>, p0: &DMatrix<f64>, max_delay_step: usize) {
        let dim_x = x.len();
        let max_delay_step = if max_delay_step > MAX_DELAY_STEP {
            log::error!(
                "requested max_delay_step {max_delay_step} exceeds the fixed cap {MAX_DELAY_STEP}; clamping."
            );
            MAX_DELAY_STEP
        } else {
            max_delay_step
        };
        let dim_x_ex = dim_x * max_delay_step;

        let mut x_ex = DVector::zeros(dim_x_ex);
        let mut p_ex = DMatrix::zeros(dim_x_ex, dim_x_ex);
        for i in 0..max_delay_step {
            let offset = i * dim_x;
            x_ex.rows_mut(offset, dim_x).copy_from(x);
            p_ex.view_mut((offset, offset), (dim_x, dim_x))
                .copy_from(p0);
        }

        self.dim_x = dim_x;
        self.max_delay_step = max_delay_step;
        self.x_ex = x_ex;
        self.p_ex = p_ex;

        self.x_next_ex = DVector::zeros(dim_x_ex);
        self.p_next_ex = DMatrix::zeros(dim_x_ex, dim_x_ex);
        self.a_transpose = DMatrix::zeros(dim_x, dim_x);
        self.ap11 = DMatrix::zeros(dim_x, dim_x);

        self.x_d = DVector::zeros(dim_x);
        self.e = DVector::zeros(MAX_DIM_Y);
        self.c_transpose = DMatrix::zeros(dim_x, MAX_DIM_Y);
        self.c_p_dd = DMatrix::zeros(MAX_DIM_Y, dim_x);
        self.s = DMatrix::zeros(MAX_DIM_Y, MAX_DIM_Y);
        self.p_ct = DMatrix::zeros(dim_x_ex, MAX_DIM_Y);
        self.k_transpose = DMatrix::zeros(MAX_DIM_Y, dim_x_ex);
        self.k = DMatrix::zeros(dim_x_ex, MAX_DIM_Y);
    }

    /// Current-time state estimate (the first `dim_x` block of the extended state).
    pub fn latest_x(&self) -> DVector<f64> {
        self.x_ex.rows(0, self.dim_x).clone_owned()
    }

    /// Current-time state covariance (the first `dim_x x dim_x` block).
    pub fn latest_p(&self) -> DMatrix<f64> {
        self.p_ex
            .view((0, 0), (self.dim_x, self.dim_x))
            .clone_owned()
    }

    /// Reads a single element of the state as it was `delay_step` predict-ticks ago.
    pub fn x_element(&self, delay_step: usize, i: usize) -> f64 {
        self.x_ex[delay_step * self.dim_x + i]
    }

    /// Advances the extended state by one predict-tick: `x_next`/`a`/`q` describe the
    /// (possibly nonlinear, already-linearized) process model for the *current* time step
    /// only; older history blocks are shifted back and kept correlated with the new
    /// current-time block through `a`, exactly as in `TimeDelayKalmanFilter::predictWithDelay`.
    ///
    /// WCET contract:
    /// - No heap allocation (all buffers were preallocated by `init()`; the new/old state
    ///   are exchanged via `core::mem::swap`, not reallocated).
    /// - No panics for `x_next`/`a`/`q` matching the `dim_x` passed to `init()` (this crate's
    ///   only caller, `EKFModule`, always builds them from that same `dim_x`).
    /// - Cost is O(dim_x^2 * max_delay_step) for the state slide and the two cross-term
    ///   blocks, plus one O(dim_x_ex^2) `copy_from` (a memcpy, not an allocation) to carry
    ///   the untouched history forward.
    /// - Does not log, format, block, or call unknown code.
    pub fn predict_with_delay(
        &mut self,
        x_next: &DVector<f64>,
        a: &DMatrix<f64>,
        q: &DMatrix<f64>,
    ) {
        let dim_x = self.dim_x;
        let dim_x_ex = dim_x * self.max_delay_step;
        let d_dim_x = dim_x_ex - dim_x;

        // Slide the state: x_next_ex = [x_next; x_ex[0..d_dim_x]].
        self.x_next_ex.rows_mut(0, dim_x).copy_from(x_next);
        if d_dim_x > 0 {
            self.x_next_ex
                .rows_mut(dim_x, d_dim_x)
                .copy_from(&self.x_ex.rows(0, d_dim_x));
        }

        // a_transpose = a^T (dim_x x dim_x, fixed-size regardless of max_delay_step).
        for i in 0..dim_x {
            for j in 0..dim_x {
                self.a_transpose[(i, j)] = a[(j, i)];
            }
        }

        // ap11 = a * p11
        {
            let p11 = self.p_ex.view((0, 0), (dim_x, dim_x));
            a.mul_to(&p11, &mut self.ap11);
        }
        // p_next_ex[0..dim_x, 0..dim_x] = ap11 * a^T + q
        {
            let mut dest = self.p_next_ex.view_mut((0, 0), (dim_x, dim_x));
            dest.copy_from(q);
            dest.gemm(1.0, &self.ap11, &self.a_transpose, 1.0);
        }

        if d_dim_x > 0 {
            // p_next_ex[0..dim_x, dim_x..] = a * p_ex[0..dim_x, 0..d_dim_x]
            {
                let p_top_strip = self.p_ex.view((0, 0), (dim_x, d_dim_x));
                let mut dest = self.p_next_ex.view_mut((0, dim_x), (dim_x, d_dim_x));
                a.mul_to(&p_top_strip, &mut dest);
            }
            // p_next_ex[dim_x.., 0..dim_x] = p_ex[0..d_dim_x, 0..dim_x] * a^T
            {
                let p_left_strip = self.p_ex.view((0, 0), (d_dim_x, dim_x));
                let mut dest = self.p_next_ex.view_mut((dim_x, 0), (d_dim_x, dim_x));
                p_left_strip.mul_to(&self.a_transpose, &mut dest);
            }
            // p_next_ex[dim_x.., dim_x..] = p_ex[0..d_dim_x, 0..d_dim_x] (unchanged history)
            {
                let p_history = self.p_ex.view((0, 0), (d_dim_x, d_dim_x));
                self.p_next_ex
                    .view_mut((dim_x, dim_x), (d_dim_x, d_dim_x))
                    .copy_from(&p_history);
            }
        }

        core::mem::swap(&mut self.x_ex, &mut self.x_next_ex);
        core::mem::swap(&mut self.p_ex, &mut self.p_next_ex);
    }

    /// Fuses a measurement `y` (with observation matrix `c` and noise covariance `r`) against
    /// the state as it was `delay_step` predict-ticks ago. Returns `false` (and leaves the
    /// filter untouched) on any dimension mismatch, an out-of-range `delay_step`, a
    /// non-invertible innovation covariance, or a NaN/Inf Kalman gain — matching upstream
    /// `TimeDelayKalmanFilter::updateWithDelay`.
    ///
    /// WCET contract:
    /// - No heap allocation, with one bounded exception: inverting the `dim_y x dim_y`
    ///   (dim_y <= `MAX_DIM_Y` = 3) innovation covariance goes through nalgebra's
    ///   `try_inverse()`, which internally clones into an owned matrix of at most 3x3 = 9
    ///   `f64` (72 bytes). This allocation is fixed-size and independent of
    ///   `max_delay_step`/`extend_state_step` — it does not grow with history depth.
    /// - Returns `false` instead of panicking on any dimension mismatch, `dim_y >
    ///   MAX_DIM_Y`, or an out-of-range `delay_step`.
    /// - Cost is O(dim_x_ex * dim_y) to build the gain and O(dim_x_ex^2) for the final
    ///   covariance subtraction (an element-wise loop over preallocated buffers, not an
    ///   allocation).
    /// - Does not log more than once per rejected call, does not block, does not call
    ///   unknown code.
    pub fn update_with_delay(
        &mut self,
        y: &DVector<f64>,
        c: &DMatrix<f64>,
        r: &DMatrix<f64>,
        delay_step: usize,
    ) -> bool {
        let dim_y = y.nrows();
        if dim_y == 0 || dim_y > MAX_DIM_Y {
            log::error!("Unsupported measurement dimension: {dim_y} (max {MAX_DIM_Y}).");
            return false;
        }
        if delay_step >= self.max_delay_step {
            log::error!(
                "Invalid delay step: {delay_step}. max_delay_step is {}. Update ignored.",
                self.max_delay_step
            );
            return false;
        }
        if c.ncols() != self.dim_x {
            log::error!(
                "Dimension mismatch in C matrix: expected {} columns, got {}.",
                self.dim_x,
                c.ncols()
            );
            return false;
        }
        if y.nrows() != c.nrows() {
            log::error!(
                "Dimension mismatch between y and C: y.rows()={}, C.rows()={}.",
                y.nrows(),
                c.nrows()
            );
            return false;
        }
        if r.nrows() != r.ncols() || r.nrows() != c.nrows() {
            log::error!("Dimension mismatch in R matrix.");
            return false;
        }

        let dim_x = self.dim_x;
        let dim_x_ex = dim_x * self.max_delay_step;
        let start_idx = dim_x * delay_step;

        self.x_d.copy_from(&self.x_ex.rows(start_idx, dim_x));

        // e[0..dim_y] = y - c * x_d
        {
            let mut e = self.e.rows_mut(0, dim_y);
            c.mul_to(&self.x_d, &mut e);
            for i in 0..dim_y {
                e[i] = y[i] - e[i];
            }
        }

        // c_transpose[0..dim_x, 0..dim_y] = c^T
        {
            let mut ct = self.c_transpose.view_mut((0, 0), (dim_x, dim_y));
            for i in 0..dim_x {
                for j in 0..dim_y {
                    ct[(i, j)] = c[(j, i)];
                }
            }
        }

        // s[0..dim_y, 0..dim_y] = r + c * p_dd * c^T
        {
            let p_dd = self.p_ex.view((start_idx, start_idx), (dim_x, dim_x));
            let mut c_p_dd = self.c_p_dd.view_mut((0, 0), (dim_y, dim_x));
            c.mul_to(&p_dd, &mut c_p_dd);
        }
        {
            let c_p_dd = self.c_p_dd.view((0, 0), (dim_y, dim_x));
            let ct = self.c_transpose.view((0, 0), (dim_x, dim_y));
            let mut s = self.s.view_mut((0, 0), (dim_y, dim_y));
            s.copy_from(r);
            s.gemm(1.0, &c_p_dd, &ct, 1.0);
        }

        // p_ct[0..dim_x_ex, 0..dim_y] = p_ex[:, start_idx..start_idx+dim_x] * c^T
        {
            let p_star_d = self.p_ex.columns(start_idx, dim_x);
            let ct = self.c_transpose.view((0, 0), (dim_x, dim_y));
            let mut p_ct = self.p_ct.view_mut((0, 0), (dim_x_ex, dim_y));
            p_star_d.mul_to(&ct, &mut p_ct);
        }

        // Bounded exception (documented in the WCET contract above): inverting a <=3x3
        // matrix clones it into an owned buffer internally.
        let s_view = self.s.view((0, 0), (dim_y, dim_y));
        let s_inv = match s_view.clone_owned().try_inverse() {
            Some(inv) => inv,
            None => {
                log::error!("Innovation covariance S is not invertible. Update ignored.");
                return false;
            }
        };

        // k[0..dim_x_ex, 0..dim_y] = p_ct * s_inv
        {
            let p_ct = self.p_ct.view((0, 0), (dim_x_ex, dim_y));
            let mut k = self.k.view_mut((0, 0), (dim_x_ex, dim_y));
            p_ct.mul_to(&s_inv, &mut k);
        }

        {
            let k = self.k.view((0, 0), (dim_x_ex, dim_y));
            if k.iter().any(|v| v.is_nan() || v.is_infinite()) {
                log::error!("Kalman gain contains NaN or Inf. Aborting update.");
                return false;
            }
        }

        // x_ex += k * e
        {
            let k = self.k.view((0, 0), (dim_x_ex, dim_y));
            let e = self.e.rows(0, dim_y);
            self.x_ex.gemm(1.0, &k, &e, 1.0);
        }

        // p_ex -= p_ct * k^T, computed in the same order as upstream
        // (`P_.noalias() -= P_CT * K.transpose();`) rather than the mathematically-equal
        // `k * p_ct^T` (which would introduce a floating-point rounding difference from a
        // different operand order, even though it is provably the same value since S^-1,
        // and hence S^-1's role in K, is symmetric). k_transpose + p_next_ex are reused
        // scratch buffers, so this still performs no allocation.
        {
            let k = self.k.view((0, 0), (dim_x_ex, dim_y));
            let mut k_t = self.k_transpose.view_mut((0, 0), (dim_y, dim_x_ex));
            for i in 0..dim_y {
                for j in 0..dim_x_ex {
                    k_t[(i, j)] = k[(j, i)];
                }
            }
        }
        {
            let p_ct = self.p_ct.view((0, 0), (dim_x_ex, dim_y));
            let k_t = self.k_transpose.view((0, 0), (dim_y, dim_x_ex));
            let mut delta = self.p_next_ex.view_mut((0, 0), (dim_x_ex, dim_x_ex));
            p_ct.mul_to(&k_t, &mut delta);
        }
        for i in 0..dim_x_ex {
            for j in 0..dim_x_ex {
                self.p_ex[(i, j)] -= self.p_next_ex[(i, j)];
            }
        }

        true
    }
}

impl Default for DelayCompensatedKalmanFilter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn identity_setup(dim_x: usize, max_delay_step: usize) -> DelayCompensatedKalmanFilter {
        let mut kf = DelayCompensatedKalmanFilter::new();
        let x0 = DVector::from_element(dim_x, 1.0);
        let p0 = DMatrix::<f64>::identity(dim_x, dim_x);
        kf.init(&x0, &p0, max_delay_step);
        kf
    }

    // [own test] no upstream equivalent.
    #[test]
    fn init_replicates_initial_state_across_all_delay_blocks() {
        let kf = identity_setup(2, 3);
        assert_eq!(kf.latest_x().len(), 2);
        for step in 0..3 {
            assert_eq!(kf.x_element(step, 0), 1.0);
            assert_eq!(kf.x_element(step, 1), 1.0);
        }
    }

    // [own test] no upstream equivalent (MAX_DELAY_STEP is this crate's own cap).
    #[test]
    fn init_clamps_max_delay_step_to_the_documented_cap() {
        let mut kf = DelayCompensatedKalmanFilter::new();
        let x0 = DVector::from_element(1, 0.0);
        let p0 = DMatrix::<f64>::identity(1, 1);
        kf.init(&x0, &p0, MAX_DELAY_STEP + 50);

        // Direct check on the clamped field, not just an indirect consequence of it.
        assert_eq!(kf.max_delay_step, MAX_DELAY_STEP);
        // dim_x = 1, so dim_x_ex == max_delay_step: confirms the buffer itself was sized
        // to the clamped value, not just that the field says so.
        assert_eq!(kf.x_ex.len(), MAX_DELAY_STEP);
        // The last valid block is at index MAX_DELAY_STEP - 1; anything beyond that would
        // have panicked on out-of-bounds access if the cap were not enforced.
        assert_eq!(kf.x_element(MAX_DELAY_STEP - 1, 0), 0.0);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn predict_with_delay_shifts_history_back() {
        let mut kf = identity_setup(1, 3);
        let a = DMatrix::<f64>::identity(1, 1);
        let q = DMatrix::<f64>::zeros(1, 1);

        kf.predict_with_delay(&DVector::from_element(1, 2.0), &a, &q);
        assert_eq!(kf.x_element(0, 0), 2.0); // newest
        assert_eq!(kf.x_element(1, 0), 1.0); // previous "now" pushed back
        assert_eq!(kf.x_element(2, 0), 1.0); // oldest history, still the initial value

        kf.predict_with_delay(&DVector::from_element(1, 3.0), &a, &q);
        assert_eq!(kf.x_element(0, 0), 3.0);
        assert_eq!(kf.x_element(1, 0), 2.0);
        assert_eq!(kf.x_element(2, 0), 1.0);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn update_with_delay_without_correlation_only_touches_targeted_block() {
        // Right after init(), each delay block's covariance is independent (`init` only
        // fills the diagonal blocks, see upstream `TimeDelayKalmanFilter::init`), so a
        // correction to block 1 must not leak into block 0.
        let mut kf = identity_setup(1, 2);
        let c = DMatrix::<f64>::identity(1, 1);
        let r = DMatrix::from_element(1, 1, 0.01);

        let ok = kf.update_with_delay(&DVector::from_element(1, 5.0), &c, &r, 1);
        assert!(ok);
        assert!(kf.x_element(1, 0) > 1.0);
        assert_eq!(kf.x_element(0, 0), 1.0);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn update_with_delay_propagates_correction_to_current_block_via_correlation() {
        // A predict tick correlates the new current block with the (now one-step-older)
        // history block through the `A*P11` cross terms, so a correction to the delayed
        // block should ripple forward into the current-time estimate too.
        let mut kf = identity_setup(1, 2);
        let a = DMatrix::<f64>::identity(1, 1);
        let q = DMatrix::<f64>::zeros(1, 1);
        kf.predict_with_delay(&DVector::from_element(1, 1.0), &a, &q);

        let c = DMatrix::<f64>::identity(1, 1);
        let r = DMatrix::from_element(1, 1, 0.01);

        let ok = kf.update_with_delay(&DVector::from_element(1, 5.0), &c, &r, 1);
        assert!(ok);
        assert!(kf.x_element(1, 0) > 1.0);
        assert!(kf.x_element(0, 0) > 1.0);
    }

    // Matches upstream test_time_delay_kalman_filter.cpp's
    // `UpdateWithInvalidDelayStepExceedsMax`. Upstream also has a separate
    // `UpdateWithNegativeDelayStep` (passing `delay_step = -1`, since upstream's
    // `delay_step` is a plain `int`): this crate uses `delay_step: usize`, so a negative
    // delay step is not a value that can be constructed at all -- the type system rules
    // it out at compile time instead of needing a runtime check/test.
    #[test]
    fn update_with_delay_rejects_out_of_range_delay_step() {
        let mut kf = identity_setup(1, 2);
        let c = DMatrix::<f64>::identity(1, 1);
        let r = DMatrix::from_element(1, 1, 0.01);

        let ok = kf.update_with_delay(&DVector::from_element(1, 5.0), &c, &r, 2);
        assert!(!ok);
        assert_eq!(kf.x_element(0, 0), 1.0);
    }

    // Matches upstream's `UpdateWithDimensionMismatchInC` (C with `dim_x + 1` columns
    // instead of `dim_x` must be rejected, not panic).
    #[test]
    fn update_with_delay_rejects_c_with_wrong_column_count() {
        let mut kf = identity_setup(3, 2);
        let c_wrong = DMatrix::<f64>::identity(3, 4); // dim_x is 3, this has 4 columns
        let r = DMatrix::<f64>::identity(3, 3);

        let ok = kf.update_with_delay(&DVector::from_element(3, 1.0), &c_wrong, &r, 0);
        assert!(!ok);
    }

    // [own test] no upstream equivalent (MAX_DIM_Y is this crate's own cap).
    #[test]
    fn update_with_delay_rejects_measurement_dimension_over_the_cap() {
        let mut kf = identity_setup(2, 2);
        let c = DMatrix::<f64>::identity(4, 2); // dim_y = 4 > MAX_DIM_Y
        let r = DMatrix::<f64>::identity(4, 4);
        let ok = kf.update_with_delay(&DVector::from_element(4, 1.0), &c, &r, 0);
        assert!(!ok);
    }

    // [own test] no upstream equivalent. Same underlying scalar Kalman update as
    // `update_with_delay_matches_hand_computed_scalar_kalman_update`, applied independently
    // across 2 decoupled dimensions (C, P0, and R are all diagonal/identity here, so there
    // is no cross-term coupling the two measurement rows): x0=1.0, P0=1.0, C=1, R=0.01,
    // y=5.0 for each dimension, giving the same K = 1/1.01 as the dim_y=1 case.
    #[test]
    fn update_with_delay_matches_a_2x2_measurement() {
        let mut kf = identity_setup(2, 1);
        let c = DMatrix::<f64>::identity(2, 2);
        let r = DMatrix::<f64>::identity(2, 2) * 0.01;

        let ok = kf.update_with_delay(&DVector::from_vec(alloc::vec![5.0, 5.0]), &c, &r, 0);
        assert!(ok);

        let k = 1.0 / 1.01;
        let expected_x = 1.0 + k * 4.0;
        assert!((kf.x_element(0, 0) - expected_x).abs() < 1e-12);
        assert!((kf.x_element(0, 1) - expected_x).abs() < 1e-12);

        let expected_p = 1.0 - k * 1.0;
        let p = kf.latest_p();
        assert!((p[(0, 0)] - expected_p).abs() < 1e-12);
        assert!((p[(1, 1)] - expected_p).abs() < 1e-12);
        // Still decoupled: no cross-term should have appeared between the two dimensions.
        assert_eq!(p[(0, 1)], 0.0);
        assert_eq!(p[(1, 0)], 0.0);
    }

    // [own test] no upstream equivalent.
    #[test]
    fn update_with_delay_matches_hand_computed_scalar_kalman_update() {
        // Golden-value check against the textbook scalar Kalman update, independent of
        // this file's implementation, to catch any operand-order regression in the
        // gemm/mul_to rewrite (e.g. accidentally computing K*P_CT^T instead of
        // P_CT*K^T -- provably the same value, but a good place for a copy-paste bug to
        // hide). x0=1.0, P0=1.0, C=1, R=0.01, y=5.0:
        //   e = y - C*x0            = 5.0 - 1.0            = 4.0
        //   S = R + C*P0*C^T        = 0.01 + 1.0           = 1.01
        //   P_CT = P0*C^T           = 1.0
        //   K = P_CT / S            = 1.0 / 1.01
        //   x1 = x0 + K*e           = 1.0 + (1.0/1.01)*4.0
        //   P1 = P0 - P_CT*K        = 1.0 - (1.0/1.01)*1.0
        let mut kf = identity_setup(1, 1);
        let c = DMatrix::<f64>::identity(1, 1);
        let r = DMatrix::from_element(1, 1, 0.01);

        let ok = kf.update_with_delay(&DVector::from_element(1, 5.0), &c, &r, 0);
        assert!(ok);

        let k = 1.0 / 1.01;
        let expected_x = 1.0 + k * 4.0;
        let expected_p = 1.0 - k * 1.0;

        assert!((kf.x_element(0, 0) - expected_x).abs() < 1e-12);
        assert!((kf.latest_p()[(0, 0)] - expected_p).abs() < 1e-12);
    }

    // --- Ground-truth cross-check, mirroring upstream test_time_delay_kalman_filter.cpp ---
    //
    // Upstream's `TimeDelayKalmanFilterTest` fixture re-derives predict/update with a
    // *second, independently written* implementation (`ground_truth_predict`/
    // `ground_truth_update`, operating on a plain full-size `Eigen::MatrixXd` with no
    // shared code with `TimeDelayKalmanFilter` itself) and checks the real implementation
    // against it, using dim_x=3/max_delay_step=5 -- large enough that a transposed block
    // or a wrong slice offset would actually be visible (the dim_x=1 tests above cannot
    // catch that class of bug, since every "matrix" involved is a 1x1 scalar). This
    // section ports that fixture and methodology, including the exact numeric values
    // upstream uses (`kInitialCovariance`=0.1, `kProcessNoise`=0.01,
    // `kMeasurementNoise`=0.001, `kStateTransitionScale`=2.0, `kObservationScale`=0.5).
    mod ground_truth {
        use nalgebra::{DMatrix, DVector};

        pub fn predict(
            x_ex: &mut DVector<f64>,
            p_ex: &mut DMatrix<f64>,
            x_next: &DVector<f64>,
            a: &DMatrix<f64>,
            q: &DMatrix<f64>,
            dim_x: usize,
            dim_x_ex: usize,
        ) {
            let d = dim_x_ex - dim_x;

            let mut x_shifted = DVector::zeros(dim_x_ex);
            x_shifted.rows_mut(dim_x, d).copy_from(&x_ex.rows(0, d));
            x_shifted.rows_mut(0, dim_x).copy_from(x_next);
            *x_ex = x_shifted;

            let mut p_tmp = DMatrix::zeros(dim_x_ex, dim_x_ex);
            let p00 = p_ex.view((0, 0), (dim_x, dim_x)).clone_owned();
            p_tmp
                .view_mut((0, 0), (dim_x, dim_x))
                .copy_from(&(a * &p00 * a.transpose() + q));
            let p0d = p_ex.view((0, 0), (dim_x, d)).clone_owned();
            p_tmp
                .view_mut((0, dim_x), (dim_x, d))
                .copy_from(&(a * &p0d));
            let pd0 = p_ex.view((0, 0), (d, dim_x)).clone_owned();
            p_tmp
                .view_mut((dim_x, 0), (d, dim_x))
                .copy_from(&(&pd0 * a.transpose()));
            let pdd = p_ex.view((0, 0), (d, d)).clone_owned();
            p_tmp.view_mut((dim_x, dim_x), (d, d)).copy_from(&pdd);
            *p_ex = p_tmp;
        }

        pub fn update(
            x_ex: &mut DVector<f64>,
            p_ex: &mut DMatrix<f64>,
            y: &DVector<f64>,
            c: &DMatrix<f64>,
            r: &DMatrix<f64>,
            delay_step: usize,
            dim_x: usize,
            dim_y: usize,
            dim_x_ex: usize,
        ) {
            let mut c_ex = DMatrix::zeros(dim_y, dim_x_ex);
            c_ex.view_mut((0, delay_step * dim_x), (dim_y, dim_x))
                .copy_from(c);

            let pct = &*p_ex * c_ex.transpose();
            let s = r + &c_ex * &pct;
            let s_inv = s
                .try_inverse()
                .expect("test fixture's S must be invertible");
            let k = &pct * s_inv;
            let y_pred = &c_ex * &*x_ex;

            *x_ex = &*x_ex + &k * (y - y_pred);
            *p_ex = &*p_ex - &k * (&c_ex * &*p_ex);
        }
    }

    struct GroundTruthFixture {
        kf: DelayCompensatedKalmanFilter,
        x_ex_gt: DVector<f64>,
        p_ex_gt: DMatrix<f64>,
        a: DMatrix<f64>,
        q: DMatrix<f64>,
        c: DMatrix<f64>,
        r: DMatrix<f64>,
    }

    const GT_DIM_X: usize = 3;
    const GT_MAX_DELAY_STEP: usize = 5;
    const GT_DIM_X_EX: usize = GT_DIM_X * GT_MAX_DELAY_STEP;
    const GT_EPSILON: f64 = 1e-5;

    impl GroundTruthFixture {
        fn new() -> Self {
            let x_t = DVector::from_vec(alloc::vec![1.0, 2.0, 3.0]);
            let p_t = DMatrix::<f64>::identity(GT_DIM_X, GT_DIM_X) * 0.1;

            let mut kf = DelayCompensatedKalmanFilter::new();
            kf.init(&x_t, &p_t, GT_MAX_DELAY_STEP);

            let mut x_ex_gt = DVector::zeros(GT_DIM_X_EX);
            let mut p_ex_gt = DMatrix::zeros(GT_DIM_X_EX, GT_DIM_X_EX);
            for i in 0..GT_MAX_DELAY_STEP {
                x_ex_gt.rows_mut(i * GT_DIM_X, GT_DIM_X).copy_from(&x_t);
                p_ex_gt
                    .view_mut((i * GT_DIM_X, i * GT_DIM_X), (GT_DIM_X, GT_DIM_X))
                    .copy_from(&p_t);
            }

            Self {
                kf,
                x_ex_gt,
                p_ex_gt,
                a: DMatrix::<f64>::identity(GT_DIM_X, GT_DIM_X) * 2.0,
                q: DMatrix::<f64>::identity(GT_DIM_X, GT_DIM_X) * 0.01,
                c: DMatrix::<f64>::identity(GT_DIM_X, GT_DIM_X) * 0.5,
                r: DMatrix::<f64>::identity(GT_DIM_X, GT_DIM_X) * 0.001,
            }
        }

        fn predict(&mut self, x_next: &DVector<f64>) {
            ground_truth::predict(
                &mut self.x_ex_gt,
                &mut self.p_ex_gt,
                x_next,
                &self.a,
                &self.q,
                GT_DIM_X,
                GT_DIM_X_EX,
            );
            self.kf.predict_with_delay(x_next, &self.a, &self.q);
        }

        fn update(&mut self, y: &DVector<f64>, delay_step: usize) -> bool {
            let c = self.c.clone();
            let r = self.r.clone();
            ground_truth::update(
                &mut self.x_ex_gt,
                &mut self.p_ex_gt,
                y,
                &c,
                &r,
                delay_step,
                GT_DIM_X,
                GT_DIM_X,
                GT_DIM_X_EX,
            );
            self.kf.update_with_delay(y, &c, &r, delay_step)
        }

        // Deliberately element-wise absolute-error, not upstream's `isApprox`-style
        // whole-vector relative error (`||A-B|| <= prec * min(||A||,||B||)`): a
        // relative/aggregate check can mask a single badly-off element when the rest of
        // the vector is large, so per-element absolute comparison is strictly more
        // sensitive here, at the cost of literal fidelity to `isApprox`'s formula.
        fn assert_matches_ground_truth(&self) {
            let x_check = self.kf.latest_x();
            let x_gt = self.x_ex_gt.rows(0, GT_DIM_X).clone_owned();
            for i in 0..GT_DIM_X {
                assert!(
                    (x_check[i] - x_gt[i]).abs() < GT_EPSILON,
                    "x[{i}]: {} vs ground truth {}",
                    x_check[i],
                    x_gt[i]
                );
            }

            let p_check = self.kf.latest_p();
            let p_gt = self
                .p_ex_gt
                .view((0, 0), (GT_DIM_X, GT_DIM_X))
                .clone_owned();
            for i in 0..GT_DIM_X {
                for j in 0..GT_DIM_X {
                    assert!(
                        (p_check[(i, j)] - p_gt[(i, j)]).abs() < GT_EPSILON,
                        "P[{i},{j}]: {} vs ground truth {}",
                        p_check[(i, j)],
                        p_gt[(i, j)]
                    );
                }
            }
        }
    }

    // Matches upstream's `TimeDelayKalmanFilterTest.Prediction`.
    #[test]
    fn predict_matches_ground_truth_reimplementation() {
        let mut fixture = GroundTruthFixture::new();
        let x_next = DVector::from_vec(alloc::vec![2.0, 4.0, 6.0]);
        fixture.predict(&x_next);
        fixture.assert_matches_ground_truth();
    }

    // Matches upstream's `TimeDelayKalmanFilterTest.UpdateWithDelay` (delay_step = 2).
    #[test]
    fn update_with_delay_at_step_2_matches_ground_truth_reimplementation() {
        let mut fixture = GroundTruthFixture::new();
        fixture.predict(&DVector::from_vec(alloc::vec![2.0, 4.0, 6.0]));

        let y_delayed = DVector::from_vec(alloc::vec![1.05, 2.05, 3.05]);
        assert!(fixture.update(&y_delayed, 2));
        fixture.assert_matches_ground_truth();
    }

    // Matches upstream's `TimeDelayKalmanFilterTest.UpdateWithZeroDelay`.
    #[test]
    fn update_with_zero_delay_matches_ground_truth_reimplementation() {
        let mut fixture = GroundTruthFixture::new();
        fixture.predict(&DVector::from_vec(alloc::vec![2.0, 4.0, 6.0]));

        let y_current = DVector::from_vec(alloc::vec![2.1, 4.1, 6.1]);
        assert!(fixture.update(&y_current, 0));
        fixture.assert_matches_ground_truth();
    }

    // Matches upstream's `TimeDelayKalmanFilterTest.UpdateWithMaxDelay` (updating the
    // oldest block in the buffer, index `max_delay_step - 1`).
    #[test]
    fn update_with_max_delay_matches_ground_truth_reimplementation() {
        let mut fixture = GroundTruthFixture::new();
        fixture.predict(&DVector::from_vec(alloc::vec![2.0, 4.0, 6.0]));

        let y_old = DVector::from_vec(alloc::vec![0.9, 1.9, 2.9]);
        assert!(fixture.update(&y_old, GT_MAX_DELAY_STEP - 1));
        fixture.assert_matches_ground_truth();
    }

    // Matches upstream's `TimeDelayKalmanFilterTest.MultiplePredictionsBeforeUpdate`.
    #[test]
    fn multiple_predictions_before_update_matches_ground_truth_reimplementation() {
        let mut fixture = GroundTruthFixture::new();

        for i in 0..3 {
            let scale = (i + 1) as f64;
            fixture.predict(&DVector::from_vec(alloc::vec![
                2.0 * scale,
                4.0 * scale,
                6.0 * scale
            ]));
        }

        let y = DVector::from_vec(alloc::vec![1.0, 2.0, 3.0]);
        assert!(fixture.update(&y, 2));
        fixture.assert_matches_ground_truth();
    }
}
