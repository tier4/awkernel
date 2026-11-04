//! Bounds-checked, panic-free access to an identity-mapped MMIO BAR window.
//!
//! WCET contract: every accessor is O(1) (one checked address computation and
//! one volatile access); `poll32` performs at most `max_iter` reads.  No
//! allocation, no blocking, no panic.

#![deny(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects,
    clippy::as_conversions,
    clippy::allow_attributes_without_reason,
    unsafe_op_in_unsafe_fn
)]

use core::ptr::{self, read_volatile, write_volatile};

use super::base_address::BaseAddress;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MmioErr {
    /// The BAR is missing or is not memory-mapped.
    NotMmio,
    /// The access falls outside the window.
    OutOfRange,
    /// Address arithmetic overflowed.
    Overflow,
    /// `poll32` exhausted its budget.
    Timeout,
}

/// A window `[base, base + len)` of mapped MMIO space.
#[derive(Debug, Clone, Copy)]
pub struct Mmio {
    base: usize,
    len: usize,
}

impl Mmio {
    /// Window covering a whole memory BAR (which must already be mapped).
    pub fn from_bar(bar: Option<BaseAddress>) -> Result<Self, MmioErr> {
        match bar {
            Some(BaseAddress::Mmio { addr, size, .. }) => Ok(Self {
                base: addr,
                len: size,
            }),
            _ => Err(MmioErr::NotMmio),
        }
    }

    fn addr(&self, off: usize, width: usize) -> Result<usize, MmioErr> {
        let end = off.checked_add(width).ok_or(MmioErr::Overflow)?;
        if end > self.len {
            return Err(MmioErr::OutOfRange);
        }
        self.base.checked_add(off).ok_or(MmioErr::Overflow)
    }

    /// `off` must be 4-byte aligned (register offsets from the device spec).
    pub fn read32(&self, off: usize) -> Result<u32, MmioErr> {
        let addr = self.addr(off, 4)?;
        // SAFETY: `addr` is inside the mapped BAR window and naturally aligned.
        Ok(unsafe { read_volatile(ptr::with_exposed_provenance::<u32>(addr)) })
    }

    /// `off` must be 4-byte aligned (register offsets from the device spec).
    pub fn write32(&self, off: usize, val: u32) -> Result<(), MmioErr> {
        let addr = self.addr(off, 4)?;
        // SAFETY: `addr` is inside the mapped BAR window and naturally aligned.
        unsafe { write_volatile(ptr::with_exposed_provenance_mut::<u32>(addr), val) };
        Ok(())
    }

    /// Write a 64-bit value as two 32-bit halves (low half first).
    pub fn write64(&self, lo_off: usize, hi_off: usize, val: u64) -> Result<(), MmioErr> {
        let [a, b, c, d, e, f, g, h] = val.to_le_bytes();
        self.write32(lo_off, u32::from_le_bytes([a, b, c, d]))?;
        self.write32(hi_off, u32::from_le_bytes([e, f, g, h]))
    }

    /// Sub-window starting at `off`.
    pub fn window(&self, off: usize) -> Result<Mmio, MmioErr> {
        let len = self.len.checked_sub(off).ok_or(MmioErr::OutOfRange)?;
        let base = self.base.checked_add(off).ok_or(MmioErr::Overflow)?;
        Ok(Mmio { base, len })
    }

    pub fn read8(&self, off: usize) -> Result<u8, MmioErr> {
        let addr = self.addr(off, 1)?;
        // SAFETY: `addr` is inside the mapped BAR window.
        Ok(unsafe { read_volatile(ptr::with_exposed_provenance::<u8>(addr)) })
    }

    /// `off` must be 2-byte aligned (register offsets from the device spec).
    pub fn read16(&self, off: usize) -> Result<u16, MmioErr> {
        let addr = self.addr(off, 2)?;
        // SAFETY: `addr` is inside the mapped BAR window and naturally aligned.
        Ok(unsafe { read_volatile(ptr::with_exposed_provenance::<u16>(addr)) })
    }

    /// Poll `off` until `(value & mask) == expected`, at most `max_iter` reads.
    pub fn poll32(
        &self,
        off: usize,
        mask: u32,
        expected: u32,
        max_iter: u32,
    ) -> Result<(), MmioErr> {
        for _ in 0..max_iter {
            if self.read32(off)? & mask == expected {
                return Ok(());
            }
            core::hint::spin_loop();
        }
        Err(MmioErr::Timeout)
    }
}
