//! # MMIO Module
//!
//! This module provides macros for defining MMIO (Memory Mapped Input/Output) operations.
//! It defines MMIO as readable, writable or both and uses either absolute addresses or offsets.
//!
//! ## Usage
//!
//! First, import the necessary items:
//!
//! ```rust
//! use awkernel_lib::{mmio_rw, mmio_r, mmio_w};
//! ```
//!
//! ### Read/Write MMIO
//!
//! You can define read/write MMIO by using the `mmio_rw!` macro.
//! This can be used with either an absolute address or an offset address:
//!
//! ```rust
//! use awkernel_lib::mmio_rw;
//!
//! fn example_rw() {
//!     mmio_rw!(0x100 => MMIO_1ST<u32>);            // Absolute address.
//!     mmio_rw!(0x200 => pub MMIO_2ND<u32>);        // Absolute address.
//!     mmio_rw!(offset 0x300 => MMIO_3RD<u32>);     // Offset address.
//!     mmio_rw!(offset 0x400 => pub MMIO_4TH<u32>); // Offset address.
//!
//!     let val = MMIO_1ST.read();       // Read from 0x100.
//!     let val = MMIO_2ND.read();       // Read from 0x200.
//!     let val = MMIO_3RD.read(0x4000); // Read from 0x4000 + 0x300.
//!     let val = MMIO_4TH.read(0x5000); // Read from 0x5000 + 0x400.
//!
//!     MMIO_1ST.write(0);         // Write a value to 0x100.
//!     MMIO_2ND.write(1);         // Write a value to 0x200.
//!     MMIO_3RD.write(2, 0x4000); // Write a value to 0x4000 + 0x300.
//!     MMIO_4TH.write(3, 0x5000); // Write a value to 0x5000 + 0x400.
//! }
//! ```
//!
//! ### Read Only MMIO
//!
//! You can define read only MMIO using the `mmio_r!` macro, in a similar way as `mmio_rw!`:
//!
//! ```rust
//! use awkernel_lib::mmio_r;
//!
//! fn example_r() {
//!     mmio_r!(0x100 => MMIO_1ST<u32>);            // Absolute address.
//!     mmio_r!(0x200 => pub MMIO_2ND<u32>);        // Absolute address.
//!     mmio_r!(offset 0x300 => MMIO_3RD<u32>);     // Offset address.
//!     mmio_r!(offset 0x400 => pub MMIO_4TH<u32>); // Offset address.
//!
//!     let val = MMIO_1ST.read();       // Read from 0x100.
//!     let val = MMIO_2ND.read();       // Read from 0x200.
//!     let val = MMIO_3RD.read(0x4000); // Read from 0x4000 + 0x300.
//!     let val = MMIO_4TH.read(0x5000); // Read from 0x5000 + 0x400.
//! }
//! ```
//!
//! ### Write Only MMIO
//!
//! You can define write only MMIO using the `mmio_w!` macro, similar to `mmio_rw!` and `mmio_r!`:
//!
//! ```rust
//! use awkernel_lib::mmio_w;
//!
//! fn exmaple_w() {
//!     mmio_w!(0x100 => MMIO_1ST<u32>);            // Absolute address.
//!     mmio_w!(0x200 => pub MMIO_2ND<u32>);        // Absolute address.
//!     mmio_w!(offset 0x300 => MMIO_3RD<u32>);     // Offset address.
//!     mmio_w!(offset 0x400 => pub MMIO_4TH<u32>); // Offset address.
//!
//!     MMIO_1ST.write(0);         // Write a value to 0x100.
//!     MMIO_2ND.write(1);         // Write a value to 0x200.
//!     MMIO_3RD.write(2, 0x4000); // Write a value to 0x4000 + 0x300.
//!     MMIO_4TH.write(3, 0x5000); // Write a value to 0x5000 + 0x400.
//! }
//! ```
//!
//! ## Bit Manipulation
//!
//! You can also perform bit manipulation operations on the MMIO objects:
//!
//! ```rust
//! use awkernel_lib::mmio_rw;
//!
//! fn example_bits() {
//!     mmio_rw!(0x100 => MMIO_1ST<u32>);
//!
//!     MMIO_1ST.setbits(1 << 4); // Make 4th bit 1.
//!     MMIO_1ST.clrbits(1 << 8); // Make 8th bit 0.
//! }
//! ```
//!
//! In the above example, `setbits` sets the specified bits to 1, and `clrbits` clears the specified bits to 0.

use core::{
    marker::PhantomData,
    ops::{BitAnd, BitOr, Not},
    ptr::{read_volatile, write_volatile},
};

/// Define read/write MMIO.
/// # Example
///
/// ```
/// use awkernel_lib::mmio_rw;
///
/// // Read/write MMIO.
/// mmio_rw!(0x100 => MMIO_1ST<u32>);            // Absolute address.
/// mmio_rw!(0x200 => pub MMIO_2ND<u32>);        // Absolute address.
/// mmio_rw!(offset 0x300 => MMIO_3RD<u32>);     // Offset address.
/// mmio_rw!(offset 0x400 => pub MMIO_4TH<u32>); // Offset address.
///
/// fn test_mmio_w() {
///     let val = MMIO_1ST.read();       // Read from 0x100.
///     let val = MMIO_2ND.read();       // Read from 0x200.
///     let val = MMIO_3RD.read(0x4000); // Read from 0x4000 + 0x300.
///     let val = MMIO_4TH.read(0x5000); // Read from 0x5000 + 0x400.
///
///     let val = MMIO_1ST.write(0);         // Write a value to 0x100.
///     let val = MMIO_2ND.write(1);         // Write a value to 0x200.
///     let val = MMIO_3RD.write(2, 0x4000); // Write a value to 0x4000 + 0x300.
///     let val = MMIO_4TH.write(3, 0x5000); // Write a value to 0x5000 + 0x400.
///
///     MMIO_1ST.clrbits(1 << 8); // Make 8th bit 0.
///     MMIO_1ST.setbits(1 << 4); // Make 4th bit 1.
/// }
/// ```
#[macro_export]
macro_rules! mmio_rw {
    ($addr:expr => $name:ident<$ty:ty>) => {
        const $name: $crate::mmio::ReadWrite<{$addr}, $ty> = $crate::mmio::ReadWrite::new();
    };
    ($addr:expr => $visibility:vis $name:ident<$ty:ty>) => {
        $visibility const $name: $crate::mmio::ReadWrite<{$addr}, $ty> = $crate::mmio::ReadWrite::new();
    };
    (offset $addr:expr => $name:ident<$ty:ty>) => {
        const $name: $crate::mmio::ReadWriteOffset<{$addr}, $ty> = $crate::mmio::ReadWriteOffset::new();
    };
    (offset $addr:expr => $visibility:vis $name:ident<$ty:ty>) => {
        $visibility const $name: $crate::mmio::ReadWriteOffset<{$addr}, $ty> = $crate::mmio::ReadWriteOffset::new();
    };
}

/// Define read only MMIO.
///
/// ```
/// use awkernel_lib::mmio_r;
///
/// // Read only MMIO.
/// mmio_r!(0x100 => MMIO_1ST<u32>);            // Absolute address.
/// mmio_r!(0x200 => pub MMIO_2ND<u32>);        // Absolute address.
/// mmio_r!(offset 0x300 => MMIO_3RD<u32>);     // Offset address.
/// mmio_r!(offset 0x400 => pub MMIO_4TH<u32>); // Offset address.
///
/// fn test_mmio_r() {
///     let val = MMIO_1ST.read();       // Read from 0x100.
///     let val = MMIO_2ND.read();       // Read from 0x200.
///     let val = MMIO_3RD.read(0x4000); // Read from 0x4000 + 0x300.
///     let val = MMIO_4TH.read(0x5000); // Read from 0x5000 + 0x400.
/// }
/// ```
#[macro_export]
macro_rules! mmio_r {
    ($addr:expr => $name:ident<$ty:ty>) => {
        const $name: $crate::mmio::ReadOnly<{$addr}, $ty> = $crate::mmio::ReadOnly::new();
    };
    ($addr:expr => $visibility:vis $name:ident<$ty:ty>) => {
        $visibility const $name: $crate::mmio::ReadOnly<{$addr}, $ty> = $crate::mmio::ReadOnly::new();
    };
    (offset $addr:expr => $name:ident<$ty:ty>) => {
        const $name: $crate::mmio::ReadOnlyOffset<{$addr}, $ty> = $crate::mmio::ReadOnlyOffset::new();
    };
    (offset $addr:expr => $visibility:vis $name:ident<$ty:ty>) => {
        $visibility const $name: $crate::mmio::ReadOnlyOffset<{$addr}, $ty> = $crate::mmio::ReadOnlyOffset::new();
    };
}

/// Define write only MMIO.
///
/// # Example
///
/// ```
/// use awkernel_lib::mmio_w;
///
/// // Write only MMIO.
/// mmio_w!(0x100 => MMIO_1ST<u32>);            // Absolute address.
/// mmio_w!(0x200 => pub MMIO_2ND<u32>);        // Absolute address.
/// mmio_w!(offset 0x300 => MMIO_3RD<u32>);     // Offset address.
/// mmio_w!(offset 0x400 => pub MMIO_4TH<u32>); // Offset address.
///
/// fn test_mmio_w() {
///     let val = MMIO_1ST.write(0);         // Write a value to 0x100.
///     let val = MMIO_2ND.write(1);         // Write a value to 0x200.
///     let val = MMIO_3RD.write(2, 0x4000); // Write a value to 0x4000 + 0x300.
///     let val = MMIO_4TH.write(3, 0x5000); // Write a value to 0x5000 + 0x400.
/// }
/// ```
#[macro_export]
macro_rules! mmio_w {
    ($addr:expr => $name:ident<$ty:ty>) => {
        const $name: $crate::mmio::WriteOnly<{$addr}, $ty> = $crate::mmio::WriteOnly::new();
    };
    ($addr:expr => $visibility:vis $name:ident<$ty:ty>) => {
        $visibility const $name: $crate::mmio::WriteOnly<{$addr}, $ty> = $crate::mmio::WriteOnly::new();
    };
    (offset $addr:expr => $name:ident<$ty:ty>) => {
        const $name: $crate::mmio::WriteOnlyOffset<{$addr}, $ty> = $crate::mmio::WriteOnlyOffset::new();
    };
    (offset $addr:expr => $visibility:vis $name:ident<$ty:ty>) => {
        $visibility const $name: $crate::mmio::WriteOnlyOffset<{$addr}, $ty> = $crate::mmio::WriteOnlyOffset::new();
    };
}

/// Read/write MMIO.
/// `BASE` is the absolute address of it.
pub struct ReadWrite<const BASE: usize, T>(PhantomData<fn() -> T>);

impl<const BASE: usize, T> ReadWrite<BASE, T>
where
    T: Not<Output = T> + BitOr<Output = T> + BitAnd<Output = T>,
{
    /// Create a mew MMIO.
    pub const fn new() -> Self {
        ReadWrite(PhantomData)
    }

    /// Read from `BASE` address.
    #[inline]
    pub fn read(&self) -> T {
        unsafe { read_volatile(BASE as *const T) }
    }

    /// Write `n` to `BASE` address.
    #[inline]
    pub fn write(&self, n: T) {
        unsafe { write_volatile(BASE as *mut T, n) }
    }

    /// Set bits.
    /// If `mask == 0b0101`, 0th and 2nd bits will be 1.
    #[inline]
    pub fn setbits(&self, mask: T) {
        let old = self.read();
        self.write(old | mask);
    }

    // Clear bits.
    /// If `mask == 0b0101`, 0th and 2nd bits will be 0.
    #[inline]
    pub fn clrbits(&self, mask: T) {
        let old = self.read();
        self.write(old & !mask);
    }
}

/// Read/write MMIO.
/// `OFFSET` is the offset address of it.
pub struct ReadWriteOffset<const OFFSET: usize, T>(PhantomData<fn() -> T>);

impl<const OFFSET: usize, T> ReadWriteOffset<OFFSET, T>
where
    T: Not<Output = T> + BitOr<Output = T> + BitAnd<Output = T>,
{
    /// Create a mew MMIO.
    pub const fn new() -> Self {
        ReadWriteOffset(PhantomData)
    }

    /// Read from `base + OFFSET` address.
    #[inline]
    pub fn read(&self, base: usize) -> T {
        unsafe { read_volatile((base + OFFSET) as *const T) }
    }

    /// Write `n` to `base + OFFSET` address.
    #[inline]
    pub fn write(&self, n: T, base: usize) {
        unsafe { write_volatile((base + OFFSET) as *mut T, n) }
    }

    /// Set bits.
    /// If `mask == 0b0101`, 0th and 2nd bits will be 1.
    #[inline]
    pub fn setbits(&self, mask: T, base: usize) {
        let old = self.read(base);
        self.write(old | mask, base);
    }

    // Clear bits.
    /// If `mask == 0b0101`, 0th and 2nd bits will be 0.
    #[inline]
    pub fn clrbits(&self, mask: T, base: usize) {
        let old = self.read(base);
        self.write(old & !mask, base);
    }

    #[inline]
    pub fn offset(&self) -> usize {
        OFFSET
    }
}

/// Read only MMIO.
/// `BASE` is the absolute address of it.
pub struct ReadOnly<const BASE: usize, T>(PhantomData<fn() -> T>);

impl<const BASE: usize, T> ReadOnly<BASE, T> {
    /// Create a new MMIO.
    pub const fn new() -> Self {
        ReadOnly(PhantomData)
    }

    /// Read from `BASE` address.
    #[inline]
    pub fn read(&self) -> T {
        unsafe { read_volatile(BASE as *const T) }
    }
}

/// Read only MMIO.
/// `OFFSET` is the absolute address of it.
pub struct ReadOnlyOffset<const OFFSET: usize, T>(PhantomData<fn() -> T>);

/// Read only MMIO.
/// `OFFSET` is the offset address of it.
impl<const OFFSET: usize, T> ReadOnlyOffset<OFFSET, T> {
    /// Create a new MMIO.
    pub const fn new() -> Self {
        ReadOnlyOffset(PhantomData)
    }

    /// Read from `base + OFFSET` address.
    #[inline]
    pub fn read(&self, base: usize) -> T {
        unsafe { read_volatile((base + OFFSET) as *const T) }
    }

    #[inline]
    pub fn offset(&self) -> usize {
        OFFSET
    }
}

/// Write only MMIO.
/// `BASE` is the absolute address of it.
pub struct WriteOnly<const BASE: usize, T>(PhantomData<fn() -> T>);

impl<const BASE: usize, T> WriteOnly<BASE, T> {
    /// Create a new MMIO.
    pub const fn new() -> Self {
        WriteOnly(PhantomData)
    }

    /// Write `n` to `BASE` address.
    #[inline]
    pub fn write(&self, n: T) {
        unsafe { write_volatile(BASE as *mut T, n) }
    }
}

/// Write only MMIO.
/// `OFFSET` is the offset address of it.
pub struct WriteOnlyOffset<const OFFSET: usize, T>(PhantomData<fn() -> T>);

impl<const OFFSET: usize, T> WriteOnlyOffset<OFFSET, T> {
    pub const fn new() -> Self {
        WriteOnlyOffset(PhantomData)
    }

    /// Write `n` to `base + OFFSET` address.
    #[inline]
    pub fn write(&self, n: T, base: usize) {
        unsafe { write_volatile((base + OFFSET) as *mut T, n) }
    }

    #[inline]
    pub fn offset(&self) -> usize {
        OFFSET
    }
}
