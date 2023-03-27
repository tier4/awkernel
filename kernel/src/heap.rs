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

use crate::arch::cpu;
use crate::{arch, config};
use core::alloc::{GlobalAlloc, Layout};
use core::intrinsics::abort;
use core::ptr::{self, NonNull};
use core::sync::atomic::{AtomicU64, Ordering};
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

#[global_allocator]
pub static TALLOC: Talloc = Talloc::new();

pub unsafe fn init() {
    TALLOC.init();
}

/// Append block into alloctor
#[cfg(feature = "x86")]
pub unsafe fn append(start: u64, end: u64) {
    TALLOC.primary.append(start, end);
}

struct Allocator(MCSLock<Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>>);
struct BackUpAllocator(MCSLock<Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>>);

pub struct Talloc {
    primary: Allocator,
    backup: BackUpAllocator,
    // bitmap for each CPU to decide which allocator to use
    flags: AtomicU64,
}

/// Using a primary allocator and a backup allocator
/// Userland only use primary allocator.
/// If OOM occurs, return the null pointer.
/// Rust will catch it and call the `alloc_error_handler`
/// Otherwise, `alloc_error_handler`,  `panic_handler`
///  and kernel would also first use the primary allocator.
/// If the primary allocator is OOM, then use the backup allocator.
/// If the backup allocator is also OOM, then abort the kernel.
unsafe impl GlobalAlloc for Talloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if self.is_primary() {
            self.primary.alloc(layout)
        } else {
            let ptr = self.primary.alloc(layout);
            if ptr.is_null() {
                return self.backup.alloc(layout);
            } else {
                return ptr;
            }
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if is_primary_mem(ptr) {
            self.primary.dealloc(ptr, layout);
        } else {
            self.backup.dealloc(ptr, layout);
        }
    }
}

impl Talloc {
    pub const fn new() -> Self {
        Self {
            primary: Allocator::new(),
            backup: BackUpAllocator::new(),
            flags: AtomicU64::new(0),
        }
    }

    pub fn init(&self) {
        unsafe {
            self.primary.init();
            self.backup.init();
        }
    }

    // switch to backup allocator
    pub unsafe fn use_backup(&self) {
        let cpu_id = cpu::cpu_id();
        let mask = !(1 << cpu_id);
        self.flags.fetch_and(mask, Ordering::SeqCst);
    }

    // switch to primary allocator
    pub unsafe fn use_primary(&self) {
        let cpu_id = cpu::cpu_id();
        let mask = 1 << cpu_id;
        self.flags.fetch_or(mask, Ordering::SeqCst);
    }

    // check whether using the primary allocator
    pub unsafe fn is_primary(&self) -> bool {
        let cpu_id = cpu::cpu_id();
        let val = self.flags.load(Ordering::SeqCst);
        (val & (1 << cpu_id)) != 0
    }
}

fn is_primary_mem(ptr: *mut u8) -> bool {
    let addr = ptr as u64;
    addr >= arch::config::HEAP_START + config::BACKUP_HEAP_SIZE
}

unsafe impl GlobalAlloc for BackUpAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut node = MCSNode::new();
        let mut guard = self.0.lock(&mut node);
        if let Some(mut ptr) = guard.allocate(layout) {
            return ptr.as_mut();
        } else {
            abort(); // there is no free memory left
        }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let mut node = MCSNode::new();
        let mut guard = self.0.lock(&mut node);
        guard.deallocate(NonNull::new_unchecked(ptr), layout.align());
    }
}

unsafe impl GlobalAlloc for Allocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut node = MCSNode::new();
        let mut guard = self.0.lock(&mut node);
        if let Some(mut ptr) = guard.allocate(layout) {
            return ptr.as_mut();
        } else {
            return ptr::null_mut();
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let mut node = MCSNode::new();
        let mut guard = self.0.lock(&mut node);
        guard.deallocate(NonNull::new_unchecked(ptr), layout.align());
    }
}

impl Allocator {
    pub const fn new() -> Self {
        Self(MCSLock::new(Tlsf::new()))
    }

    pub unsafe fn init(&self) {
        let primary_heap_start = (config::HEAP_START + config::BACKUP_HEAP_SIZE) as *mut u8;
        let primary_heap_size = (config::HEAP_SIZE - config::BACKUP_HEAP_SIZE) as usize;
        let primary_heap_mem =
            core::slice::from_raw_parts_mut(primary_heap_start, primary_heap_size);

        let Some(heap_mem) = NonNull::new(primary_heap_mem) else { return; };

        // Insert primary heap memory .
        let mut node = MCSNode::new();
        let mut guard = self.0.lock(&mut node);
        guard.insert_free_block_ptr(heap_mem);
    }

    #[cfg(feature = "x86")]
    pub unsafe fn append(&self, start: u64, end: u64) {
        let append_heap_start = start as *mut u8;
        let append_heap_size = (end - start) as usize;
        let append_heap_mem = core::slice::from_raw_parts_mut(append_heap_start, append_heap_size);

        let Some(heap_mem) = NonNull::new(append_heap_mem) else { return; };

        // Insert append heap memory .
        let mut node = MCSNode::new();
        let mut guard = self.0.lock(&mut node);
        guard.append_free_block_ptr(heap_mem);
    }
}

impl BackUpAllocator {
    pub const fn new() -> Self {
        Self(MCSLock::new(Tlsf::new()))
    }

    pub unsafe fn init(&self) {
        let backup_heap_start = arch::config::HEAP_START;
        let backup_heap_size = config::BACKUP_HEAP_SIZE as usize;
        let backup_heap_mem =
            core::slice::from_raw_parts_mut(backup_heap_start as *mut u8, backup_heap_size);

        let Some(heap_mem) = NonNull::new(backup_heap_mem) else { return; };

        // Insert backup heap memory .
        let mut node = MCSNode::new();
        let mut guard = self.0.lock(&mut node);
        guard.insert_free_block_ptr(heap_mem);
    }
}
