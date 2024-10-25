//! A allocator which uses a dedicated memory region.
//! This can be used for `Box`, `Vec`, etc. instead of the global allocator.
//!
//! # Example
//!
//! ```
//! #![feature(allocator_api)]
//!
//! use awkernel_lib::local_heap::{TLSF, LocalHeap};
//! use core::{cell::RefCell, mem::MaybeUninit};
//!
//! let mut memory_pool = [MaybeUninit::new(0); 1024];
//! let tlsf: RefCell<TLSF> = RefCell::new(TLSF::new(&mut memory_pool));
//! let alloc = LocalHeap::new(&tlsf);
//!
//! // create a `Box`
//! let value = Box::new_in(100, alloc.clone());
//! ```

use core::{alloc::Allocator, cell::RefCell, mem::MaybeUninit, ptr::NonNull};
use rlsf::int::BinInteger;

const FLLEN_DEFAULT: usize = 14; // The maximum block size is (32 << 14) - 1 = 512KiB - 1
const SLLEN_DEFAULT: usize = 32; // The worst-case internal fragmentation is ((32 << 14) / 64 - 2) = 8190
type FLBitmapDefault = u16; // must be equal to or larger than FLLEN
type SLBitmapDefault = u32; // must be equal to or longer than SLLEN

/// TLSF O(1) memory allocator.
///
/// # Default Configuration
///
/// - `FLBitmap = 14`: The maximum block size is (32 << 14) - 1 = 512KiB - 1
/// - `SLBitmap =  64`: The worst-case internal fragmentation is ((32 << 14) / 64 - 2) = 8190
pub struct TLSF<
    'pool,
    FLBitmap = FLBitmapDefault,
    SLBitmap = SLBitmapDefault,
    const FLLEN: usize = FLLEN_DEFAULT,
    const SLLEN: usize = SLLEN_DEFAULT,
> {
    allocator: rlsf::Tlsf<'pool, FLBitmap, SLBitmap, FLLEN, SLLEN>,
}

impl<'pool, FLBitmap, SLBitmap, const FLLEN: usize, const SLLEN: usize>
    TLSF<'pool, FLBitmap, SLBitmap, FLLEN, SLLEN>
where
    FLBitmap: BinInteger,
    SLBitmap: BinInteger,
{
    pub fn new(memory_pool: &'pool mut [MaybeUninit<u8>]) -> Self {
        let mut allocator = rlsf::Tlsf::new();
        allocator.insert_free_block(memory_pool);

        Self { allocator }
    }
}

/// A local heap allocator.
#[derive(Clone)]
pub struct LocalHeap<
    'a,
    'pool,
    FLBitmap = FLBitmapDefault,
    SLBitmap = SLBitmapDefault,
    const FLLEN: usize = FLLEN_DEFAULT,
    const SLLEN: usize = SLLEN_DEFAULT,
> {
    tlsf: &'a RefCell<TLSF<'pool, FLBitmap, SLBitmap, FLLEN, SLLEN>>,
}

impl<'a, 'pool, FLBitmap, SLBitmap, const FLLEN: usize, const SLLEN: usize>
    LocalHeap<'a, 'pool, FLBitmap, SLBitmap, FLLEN, SLLEN>
{
    pub fn new(tlsf: &'a RefCell<TLSF<'pool, FLBitmap, SLBitmap, FLLEN, SLLEN>>) -> Self {
        Self { tlsf }
    }
}

unsafe impl<FLBitmap, SLBitmap, const FLLEN: usize, const SLLEN: usize> Allocator
    for LocalHeap<'_, '_, FLBitmap, SLBitmap, FLLEN, SLLEN>
where
    FLBitmap: BinInteger,
    SLBitmap: BinInteger,
{
    fn allocate(
        &self,
        layout: core::alloc::Layout,
    ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
        let tlsf = &mut self.tlsf.borrow_mut().allocator;

        if let Some(ptr) = tlsf.allocate(layout) {
            Ok(NonNull::slice_from_raw_parts(ptr, layout.size()))
        } else {
            Err(core::alloc::AllocError)
        }
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: core::alloc::Layout) {
        let ptr = ptr.as_ptr();
        let tlsf = &mut self.tlsf.borrow_mut().allocator;
        tlsf.deallocate(NonNull::new_unchecked(ptr), layout.align());
    }
}

#[cfg(test)]
mod test {
    use alloc::{boxed::Box, vec::Vec};

    use super::*;

    #[test]
    fn test_local_heap() {
        let mut memory_pool = [MaybeUninit::new(0); 1024];
        let tlsf: RefCell<TLSF> = RefCell::new(TLSF::new(&mut memory_pool));
        let alloc = LocalHeap::new(&tlsf);

        let _a = Box::new_in(100, alloc.clone());
        let mut b = Vec::new_in(alloc);
        b.push(20);
    }
}
