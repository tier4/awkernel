#[allow(dead_code)]
#[derive(Debug)]
pub enum InitErr {
    InvalidPhysicalMemoryOffset,
    InvalidACPI,
    FailedToAllocateFrame,
    FailedToMapPage,
}


static mut HEAP: [MaybeUninit<u8>; 256 * 1024 * 1024] = [MaybeUninit::uninit(); 256 * 1024 * 1024];
 
pub fn init() {
    // Initialize memory allocator.
    
    let mut node = MCSNode::new();
    let mut guard = TALLOC.0.lock(&mut node);
    unsafe { guard.insert_free_block(&mut HEAP); } 

}

use core::mem::MaybeUninit;
use synctools::mcs::{MCSLock, MCSNode};
use rlsf::Tlsf;
use core::ptr::NonNull;
use core::alloc::GlobalAlloc;


struct Allocator<'pool, FLBitmap, SLBitmap, const FLLEN: usize, const SLLEN: usize>
(MCSLock<Tlsf<'pool, FLBitmap, SLBitmap, FLLEN, SLLEN>>);

#[global_allocator]
static TALLOC : Allocator<'_, u16, u16, 12, 16> = Allocator(MCSLock::new(Tlsf::new()));



unsafe impl<'pool> GlobalAlloc for Allocator<'_, u16, u16, 12, 16> {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        let mut node = MCSNode::new();
        let mut guard = TALLOC.0.lock(&mut node);
        guard.allocate(layout).unwrap().as_mut()
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
        let mut node = MCSNode::new();
        let mut guard = TALLOC.0.lock(&mut node);
        guard.deallocate(NonNull::new_unchecked(ptr), layout.align());
    }
}