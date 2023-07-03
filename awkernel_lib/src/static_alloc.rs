use core::{alloc::Allocator, mem::MaybeUninit, ptr::NonNull};

use rlsf::int::BinInteger;

const FLLEN_DEFAULT: usize = 14; // The maximum block size is (32 << 14) - 1 = 512KiB - 1
const SLLEN_DEFAULT: usize = 64; // The worst-case internal fragmentation is ((32 << 14) / 64 - 2) = 8190
type FLBitmapDefault = u16; // must be equal to or larger than FLLEN
type SLBitmapDefault = u64; // must be equal to or longer than SLLEN

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

#[derive(Clone)]
pub struct StaticAlloc<
    'pool,
    FLBitmap = FLBitmapDefault,
    SLBitmap = SLBitmapDefault,
    const FLLEN: usize = FLLEN_DEFAULT,
    const SLLEN: usize = SLLEN_DEFAULT,
> {
    tlsf: *mut TLSF<'pool, FLBitmap, SLBitmap, FLLEN, SLLEN>,
}

impl<'pool, FLBitmap, SLBitmap, const FLLEN: usize, const SLLEN: usize>
    StaticAlloc<'pool, FLBitmap, SLBitmap, FLLEN, SLLEN>
{
    pub fn new(tlsf: &mut TLSF<'pool, FLBitmap, SLBitmap, FLLEN, SLLEN>) -> Self {
        Self {
            tlsf: tlsf as *mut _,
        }
    }
}

unsafe impl<'pool, FLBitmap, SLBitmap, const FLLEN: usize, const SLLEN: usize> Allocator
    for StaticAlloc<'pool, FLBitmap, SLBitmap, FLLEN, SLLEN>
where
    FLBitmap: BinInteger,
    SLBitmap: BinInteger,
{
    fn allocate(
        &self,
        layout: core::alloc::Layout,
    ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
        let tlsf = unsafe { &mut (*self.tlsf).allocator };

        if let Some(ptr) = tlsf.allocate(layout) {
            Ok(NonNull::slice_from_raw_parts(ptr, layout.size()))
        } else {
            Err(core::alloc::AllocError)
        }
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: core::alloc::Layout) {
        let ptr = ptr.as_ptr();
        let tlsf = unsafe { &mut (*self.tlsf).allocator };
        tlsf.deallocate(NonNull::new_unchecked(ptr), layout.align());
    }
}
