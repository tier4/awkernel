//! Pure helpers for heap layout math.
//!
//! These live outside the `heap` module (which is `#[cfg(not(feature = "std"))]`, because
//! it installs the `#[global_allocator]`) so they can be unit-tested by the host
//! `--features std` test build, which does not compile the `heap` module.

/// Rounds `value` up to the next multiple of `align`, which must be a power of two.
/// Returns `None` if the rounding would overflow `usize`.
///
/// Used by the `wf_alloc` backend's layout math in [`crate::heap`]. Gated to compile when
/// that backend is active or under `cfg(test)`, so it is exercised by the unit tests below
/// without pulling the `heap-wf-alloc` feature (and the `wf_alloc` dependency) into the
/// test build.
#[cfg(any(
    all(
        feature = "heap-wf-alloc",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ),
    test
))]
pub(crate) fn align_up(value: usize, align: usize) -> Option<usize> {
    debug_assert!(align.is_power_of_two());
    value
        .checked_add(align - 1)
        .map(|value| value & !(align - 1))
}

#[cfg(test)]
mod tests {
    use super::align_up;

    #[test]
    fn align_up_already_aligned_is_unchanged() {
        assert_eq!(align_up(0, 4), Some(0));
        assert_eq!(align_up(8, 4), Some(8));
        assert_eq!(align_up(65536, 65536), Some(65536));
    }

    #[test]
    fn align_up_rounds_up_to_next_multiple() {
        assert_eq!(align_up(1, 4), Some(4));
        assert_eq!(align_up(5, 4), Some(8));
        assert_eq!(align_up(7, 4), Some(8));
        // Large power-of-two alignment, as used for the metadata / span regions.
        assert_eq!(align_up(1, 65536), Some(65536));
        assert_eq!(align_up(65537, 65536), Some(131072));
    }

    #[test]
    fn align_up_with_alignment_one_is_identity() {
        assert_eq!(align_up(0, 1), Some(0));
        assert_eq!(align_up(123, 1), Some(123));
        assert_eq!(align_up(usize::MAX, 1), Some(usize::MAX));
    }

    #[test]
    fn align_up_overflow_returns_none() {
        assert_eq!(align_up(usize::MAX, 2), None);
        assert_eq!(align_up(usize::MAX - 1, 4), None);
        // The largest value that still fits for a given alignment is rounded normally.
        let aligned_max = usize::MAX & !(4 - 1);
        assert_eq!(align_up(aligned_max, 4), Some(aligned_max));
    }
}
