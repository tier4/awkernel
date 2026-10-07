//! Data cache maintenance by virtual address.

use crate::{ctr_el0, dsb_sy};
use core::arch::asm;

/// Smallest D-cache line size, in bytes, as reported by `CTR_EL0.DminLine`.
#[inline(always)]
pub fn dcache_line_size() -> usize {
    let dmin_line = ((ctr_el0::get() >> 16) & 0xf) as usize; // log2 of the line size in words
    4usize << dmin_line
}

/// Applies `op` to every D-cache line overlapping `[addr, addr + len)`, then waits for completion.
#[inline(always)]
fn for_each_line(addr: usize, len: usize, op: impl Fn(usize)) {
    let line_size = dcache_line_size();
    let end = addr.saturating_add(len);
    let mut line = addr & !line_size.wrapping_sub(1);

    while line < end {
        op(line);
        match line.checked_add(line_size) {
            Some(next) => line = next,
            None => break,
        }
    }

    dsb_sy();
}

/// Writes back (`dc cvac`) the D-cache lines covering `[addr, addr + len)` to the point of coherency.
///
/// # Safety
///
/// `[addr, addr + len)` must be mapped, or the cache operation faults.
#[inline]
pub unsafe fn clean_dcache_range(addr: usize, len: usize) {
    for_each_line(addr, len, |line| unsafe {
        asm!("dc cvac, {}", in(reg) line, options(nostack, preserves_flags));
    });
}

/// Invalidates (`dc ivac`) the D-cache lines covering `[addr, addr + len)`, discarding dirty data.
///
/// # Safety
///
/// `[addr, addr + len)` must be mapped. Lines shared with data outside the range lose their
/// unwritten updates, so the range must be cache-line aligned and sized.
#[inline]
pub unsafe fn invalidate_dcache_range(addr: usize, len: usize) {
    for_each_line(addr, len, |line| unsafe {
        asm!("dc ivac, {}", in(reg) line, options(nostack, preserves_flags));
    });
}
