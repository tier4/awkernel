//! Use a second-level segregated list.
//! `FLLEN` represents the length of first level lists.
//! `SLLEN` represents the length of second level lists.
//!
//! `minimum_size = size_of::<usize>() * 4`
//!
//! For example, on a 64-bit system, the minimum block size is `minimum_size = size_of::<usize>() * 4 = 32` bytes,
//! while the maximum block size is `(32 << FLLEN) - 1`.
//! The maximum size requested  should be smaller than this.
//! The worst-case internal fragmentation is `(32 << FLLEN) / SLLEN - 2` bytes.
//!
//! # Limitation
//!
//! Only 32 or 64 CPUs are supported for 32 or 64 bits CPU architectures.
//!
//! # Example
//!
//! ## Switch Allocators
//!
//! ```
//! use awkernel_lib::heap;
//!
//! // Use only the primary allocator.
//! unsafe { heap::Talloc::use_primary() };
//!
//! // Use both the primary and backup allocators.
//! unsafe { heap::Talloc::use_primary_then_backup() };
//! ```
//!
//! ## Save Configuration
//!
//! ```
//! // Save current configuration.
//! let guard = heap::Talloc::save();
//!
//! // Switch to use only the primary allocator.
//! unsafe { heap::Talloc::use_primary() };
//!
//! // Restore the configuration.
//! drop(guard)
//! ```

const FLLEN: usize = 28; // The maximum block size is (32 << 28) - 1 = 8_589_934_591 (nearly 8GiB)
const SLLEN: usize = 64; // The worst-case internal fragmentation is ((32 << 28) / 64 - 2) = 134_217_726 (nearly 128MiB)
type FLBitmap = u32; // must be longer than FLLEN
type SLBitmap = u64; // must be longer than SLLEN

use crate::{
    console::unsafe_puts,
    cpu::{self, NUM_MAX_CPU},
    sync::{mcs::MCSNode, mutex::Mutex},
};
use core::{
    alloc::{GlobalAlloc, Layout},
    intrinsics::abort,
    mem::transmute,
    ptr::{self, NonNull},
    sync::atomic::{AtomicU32, AtomicUsize, Ordering},
};
use rlsf::Tlsf;

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

/// # Safety
///
/// This must be called at initialization.
pub unsafe fn init_primary(primary_start: usize, primary_size: usize) {
    TALLOC.init_primary(primary_start, primary_size);
}

/// # Safety
///
/// This must be called at initialization.
pub unsafe fn init_backup(backup_start: usize, backup_size: usize) {
    TALLOC.init_backup(backup_start, backup_size);
}

type TLSFAlloc = Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>;

struct Allocator(Mutex<TLSFAlloc>);
struct BackUpAllocator(Mutex<TLSFAlloc>);

pub struct Talloc {
    primary: Allocator,
    backup: BackUpAllocator,

    /// bitmap for each CPU to decide which allocator to use
    flags: [AtomicU32; NUM_MAX_CPU / 32],

    primary_start: AtomicUsize,
    primary_size: AtomicUsize,
    backup_start: AtomicUsize,
    backup_size: AtomicUsize,
}

/// `Talloc` uses the primary and backup allocators.
///
/// In the userland, only the primary allocator will be used.
/// If OOM occurs in the userland, the primary allocator returns the null pointer and
/// invokes the OOM handler, `alloc_error_handler`.
///
/// Otherwise, the kernel will first use the primary allocator.
/// If the primary allocator is exhausted, then the kernel uses the backup allocator.
/// If the backup allocator is also exhausted, then the kernel will aborted.
unsafe impl GlobalAlloc for Talloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if self.is_primary() {
            let ptr = self.primary.alloc(layout);
            if ptr.is_null() {
                panic!();
            } else {
                ptr
            }
        } else {
            let ptr = self.primary.alloc(layout);
            if ptr.is_null() {
                self.backup.alloc(layout)
            } else {
                ptr
            }
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if self.is_primary_mem(ptr) {
            self.primary.dealloc(ptr, layout);
        } else {
            self.backup.dealloc(ptr, layout);
        }
    }
}

pub struct Guard<'a> {
    talloc: &'a Talloc,
    index: usize,
    flag: u32,
}

impl<'a> Drop for Guard<'a> {
    fn drop(&mut self) {
        unsafe { self.talloc.restore(self.index, self.flag) };
    }
}

impl Talloc {
    pub const fn new() -> Self {
        let flags = [0; NUM_MAX_CPU / 32];

        Self {
            primary: Allocator::new(),
            backup: BackUpAllocator::new(),
            flags: unsafe { transmute(flags) },
            primary_start: AtomicUsize::new(0),
            primary_size: AtomicUsize::new(0),
            backup_start: AtomicUsize::new(0),
            backup_size: AtomicUsize::new(0),
        }
    }

    pub fn init_primary(&self, primary_start: usize, primary_size: usize) {
        self.primary_start.store(primary_start, Ordering::Relaxed);
        self.primary_size.store(primary_size, Ordering::Relaxed);

        unsafe { self.primary.init(primary_start, primary_size) };
    }

    pub fn init_backup(&self, backup_start: usize, backup_size: usize) {
        self.backup_start.store(backup_start, Ordering::Relaxed);
        self.backup_size.store(backup_size, Ordering::Relaxed);

        unsafe { self.backup.init(backup_start, backup_size) };
    }

    fn cpu_index() -> (usize, u32) {
        let cpu_id = cpu::cpu_id();
        let index = cpu_id >> 5;
        let id = cpu_id & (32 - 1);
        (index, id as u32)
    }

    /// use both the primary and backup allocators
    /// # Safety
    ///
    /// After calling this function, the heap memory allocator uses both the primary and backup allocators.
    pub unsafe fn use_primary_then_backup(&self) {
        let (index, cpu_id) = Self::cpu_index();
        let mask = !(1 << cpu_id);
        self.flags[index].fetch_and(mask, Ordering::Relaxed);
    }

    /// use only the primary allocator
    ///
    /// # Safety
    ///
    /// After calling this function, the heap memory allocator uses only the primary allocator.
    pub unsafe fn use_primary(&self) {
        let (index, cpu_id) = Self::cpu_index();
        let mask = 1 << cpu_id;
        self.flags[index].fetch_or(mask, Ordering::Relaxed);
    }

    /// Save the configuration and it will be restored when dropping `Guard`.
    pub fn save(&self) -> Guard {
        let (index, cpu_id) = Self::cpu_index();
        let mask = 1 << cpu_id;
        let flag = mask & self.flags[index].load(Ordering::Relaxed);
        Guard {
            talloc: self,
            index,
            flag,
        }
    }

    unsafe fn restore(&self, index: usize, flag: u32) {
        self.flags[index].fetch_or(flag, Ordering::Relaxed);
    }

    /// check whether using the primary allocator
    pub fn is_primary(&self) -> bool {
        let (index, cpu_id) = Self::cpu_index();
        let val = self.flags[index].load(Ordering::Relaxed);
        (val & (1 << cpu_id)) != 0
    }

    pub fn is_primary_mem(&self, ptr: *mut u8) -> bool {
        let addr = ptr as usize;
        let start = self.primary_start.load(Ordering::Relaxed);
        let end = start + self.primary_size.load(Ordering::Relaxed);

        (start..end).contains(&addr)
    }
}

unsafe impl GlobalAlloc for BackUpAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut node = MCSNode::new();
        let mut guard = self.0.lock(&mut node);
        if let Some(mut ptr) = guard.allocate(layout) {
            return ptr.as_mut();
        } else {
            drop(guard);
            unsafe_puts("failed to allocate heap memory\r\n");
            unsafe_puts("aborting...\r\n");
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
            ptr.as_mut()
        } else {
            ptr::null_mut()
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
        Self(Mutex::new(Tlsf::new()))
    }

    pub unsafe fn init(&self, heap_start: usize, heap_size: usize) {
        let mut node = MCSNode::new();
        let mut guard = self.0.lock(&mut node);
        init_heap(&mut guard, heap_start, heap_size);
    }
}

impl BackUpAllocator {
    pub const fn new() -> Self {
        Self(Mutex::new(Tlsf::new()))
    }

    pub unsafe fn init(&self, heap_start: usize, heap_size: usize) {
        let mut node = MCSNode::new();
        let mut guard = self.0.lock(&mut node);
        init_heap(&mut guard, heap_start, heap_size);
    }
}

unsafe fn init_heap(allocator: &mut TLSFAlloc, heap_start: usize, heap_size: usize) {
    let heap_mem = core::slice::from_raw_parts_mut(heap_start as *mut u8, heap_size);
    let Some(heap_mem) = NonNull::new(heap_mem) else { return; };
    allocator.insert_free_block_ptr(heap_mem);
}
