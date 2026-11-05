//! Placement of a transfer buffer under the xHCI 64 KiB rule.
//!
//! The data buffer of a transfer TRB must not span a 64 KiB boundary (xHCI
//! spec §6.4.1, Data Buffer Pointer of the Normal and Data Stage TRBs).  A
//! data stage of up to 65535 bytes (wLength) therefore fits one TRB if the
//! buffer is placed in a window that does not cross one.

/// The boundary a TRB data buffer must not cross.
pub const TRB_BOUNDARY: u64 = 0x1_0000;

/// Offset of a `len`-byte window that does not cross a 64 KiB boundary,
/// within a buffer of `buf_len` bytes at physical address `phys`.
///
/// The window starts at `phys` if it fits before the next boundary, and at
/// that boundary otherwise.  `None` if `len` exceeds 64 KiB or the window does
/// not fit the buffer.  A buffer of `2 * TRB_BOUNDARY` bytes always fits any
/// `len` up to `TRB_BOUNDARY`, wherever it is placed.
pub fn window_offset(phys: u64, buf_len: usize, len: usize) -> Option<usize> {
    let len64 = u64::try_from(len).ok()?;
    if len64 > TRB_BOUNDARY {
        return None;
    }
    let into = phys.checked_rem(TRB_BOUNDARY)?;
    let offset = if into.checked_add(len64)? <= TRB_BOUNDARY {
        0
    } else {
        TRB_BOUNDARY.checked_sub(into)?
    };
    let offset = usize::try_from(offset).ok()?;
    (offset.checked_add(len)? <= buf_len).then_some(offset)
}

#[cfg(test)]
mod tests {
    use super::*;

    const BOUNDARY: usize = 0x1_0000;

    /// The window `[phys + offset, phys + offset + len)` crosses no boundary.
    fn within_one_block(phys: u64, offset: usize, len: usize) -> bool {
        if len == 0 {
            return true;
        }
        let start = phys + u64::try_from(offset).unwrap();
        let last = start + u64::try_from(len).unwrap() - 1;
        start / TRB_BOUNDARY == last / TRB_BOUNDARY
    }

    #[test]
    fn keeps_a_window_that_fits_before_the_boundary() {
        assert_eq!(window_offset(0x10_0000, 4096, 4096), Some(0));
        assert_eq!(window_offset(0x10_f000, 2 * BOUNDARY, 4096), Some(0));
    }

    #[test]
    fn moves_a_window_that_would_cross_to_the_boundary() {
        // 0x10_f000 + 5000 crosses 0x11_0000; the window starts there instead.
        assert_eq!(window_offset(0x10_f000, 2 * BOUNDARY, 5000), Some(0x1000));
    }

    /// Any page-aligned placement of a 128 KiB buffer holds a 65535-byte
    /// window (the longest wTotalLength) that crosses no boundary.
    #[test]
    fn a_two_block_buffer_always_holds_the_longest_data_stage() {
        for page in 0..32 {
            let phys = 0x40_0000 + page * 0x1000;
            let offset = window_offset(phys, 2 * BOUNDARY, 65535).unwrap();
            assert!(offset + 65535 <= 2 * BOUNDARY);
            assert!(within_one_block(phys, offset, 65535));
        }
    }

    #[test]
    fn rejects_a_window_that_cannot_fit() {
        assert_eq!(window_offset(0, 2 * BOUNDARY, BOUNDARY + 1), None);
        assert_eq!(window_offset(0x10_f000, 8192, 5000), None);
    }
}
