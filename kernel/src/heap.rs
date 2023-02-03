//! Using a second-level segregated list.
//! FLLEN represents the length of first level lists.
//! SLLEN represents the length of second level lists.
//!
//! `minimum_size = size_of::<usize>() * 4`
//!
//! For example, on a 64-bit system, the minimum block size is `minimum_size = size_of::<usize>() * 4 = 32` bytes,
//! while the maximum block size is `(32 << FLLEN) - 1`.
//! The maximum size requested  should be smaller than this.
//! The worst-case internal fragmentation is `(32 << FLLEN) / SLLEN - 2` bytes.

const FLLEN: usize = 28; // The maximum block size is (32 << 28) - 1 = 8_589_934_591 (nearly 8GiB)
const SLLEN: usize = 64; // The worst-case internal fragmentation is ((32 << 28) / 64 - 2) = 134_217_726 (nearly 128MiB)
type FLBitmap = u32; // must be longer than FLLEN
type SLBitmap = u64; // must be longer than SLLEN

use crate::{arch, config};
use core::alloc::{GlobalAlloc, Layout};
use core::ptr::NonNull;
use rlsf::Tlsf;
use synctools::mcs::{MCSLock, MCSNode};

#[allow(dead_code)]
#[derive(Debug)]
pub enum InitErr {
    InvalidPhysicalMemoryOffset,
    InvalidACPI,
    FailedToAllocateFrame,
    FailedToMapPage,
}

pub fn init() {
    let ptr = arch::config::HEAP_START as *mut u8;
    let heap_mem = unsafe { core::slice::from_raw_parts_mut(ptr, config::HEAP_SIZE as usize) };

    let Some(heap_mem) = NonNull::new(heap_mem) else { return; };

    // Initialize memory allocator.
    let mut node = MCSNode::new();
    let mut guard = TALLOC.0.lock(&mut node);
    unsafe {
        guard.insert_free_block_ptr(heap_mem);
    }
}

struct Allocator(MCSLock<Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>>);

#[global_allocator]
static TALLOC: Allocator = Allocator(MCSLock::new(Tlsf::new()));

unsafe impl GlobalAlloc for Allocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut node = MCSNode::new();
        let mut guard = TALLOC.0.lock(&mut node);
        guard.allocate(layout).unwrap().as_mut()
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let mut node = MCSNode::new();
        let mut guard = TALLOC.0.lock(&mut node);
        guard.deallocate(NonNull::new_unchecked(ptr), layout.align());
    }
}
