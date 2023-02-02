#[allow(dead_code)]
#[derive(Debug)]
pub enum InitErr {
    InvalidPhysicalMemoryOffset,
    InvalidACPI,
    FailedToAllocateFrame,
    FailedToMapPage,
}


static mut HEAP: [MaybeUninit<u8>; 16 * 1024 * 1024] = [MaybeUninit::uninit(); 16 * 1024 * 1024];
 
pub fn init() {
    // Initialize memory allocator.
    let mut node = MCSNode::new();
    let mut guard = TALLOC.0.lock(&mut node);
    unsafe { guard.insert_free_block(&mut HEAP); } 

}

use core::mem::MaybeUninit;
use core::alloc::{GlobalAlloc, Layout};
use synctools::mcs::{MCSLock, MCSNode};
use rlsf::Tlsf;
use core::ptr::NonNull;


// Using a second-level segregated list
// FLLEN represents the length of first level lists 
// SLLEN represents the length of second level lists
// For example, on a 32-bit system, the minimum block size is 16 bytes, 
// while the maximum block size is  (16 << FLLEN) - 1. 
// The maximum size requested  should be smaller than this. 
// The worst-case internal fragmentation is (16 << FLLEN) / SLLEN - 2 = 4094 bytes. 

const FLLEN : usize = 12;
const SLLEN : usize = 16; 
type FLBitmap = u16;  // must be longer than FILLEN
type SLBitmap = u16;  // must be longer than SILLEN  


struct Allocator(MCSLock<Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>>);

#[global_allocator]
static TALLOC : Allocator = Allocator(MCSLock::new(Tlsf::new()));



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