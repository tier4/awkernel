//! Use a second-level segregated list.
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

use crate::cpu;
use core::{
    alloc::{GlobalAlloc, Layout},
    intrinsics::abort,
    ptr::{self, NonNull},
    sync::atomic::{AtomicU64, AtomicUsize, Ordering},
};
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

pub unsafe fn init_primary(primary_start: usize, primary_size: usize) {
    TALLOC.init_primary(primary_start, primary_size);
}

pub unsafe fn init_backup(backup_start: usize, backup_size: usize) {
    TALLOC.init_backup(backup_start, backup_size);
}

type TLSFAlloc = Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>;

struct Allocator(MCSLock<TLSFAlloc>);
struct BackUpAllocator(MCSLock<TLSFAlloc>);

pub struct Talloc {
    primary: Allocator,
    backup: BackUpAllocator,

    /// bitmap for each CPU to decide which allocator to use
    flags: AtomicU64,

    primary_start: AtomicUsize,
    primary_size: AtomicUsize,
    backup_start: AtomicUsize,
    backup_size: AtomicUsize,
}

/// Use a primary allocator and a backup allocator.
/// In the userland, only the primary allocator is used.
/// If OOM occurs in the userland, the primary allocator returns the null pointer,
/// caught it by the OOM handler and `alloc_error_handler` is called.
/// Otherwise, `alloc_error_handler`,  `panic_handler`
/// and kernel would also first use the primary allocator.
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
        if self.is_primary_mem(ptr) {
            self.primary.dealloc(ptr, layout);
        } else {
            self.backup.dealloc(ptr, layout);
        }
    }
}

pub struct Guard<'a> {
    talloc: &'a Talloc,
    flag: u64,
}

impl<'a> Drop for Guard<'a> {
    fn drop(&mut self) {
        unsafe { self.talloc.restore(self.flag) };
    }
}

impl Talloc {
    pub const fn new() -> Self {
        Self {
            primary: Allocator::new(),
            backup: BackUpAllocator::new(),
            flags: AtomicU64::new(0),
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

    /// switch to backup allocator
    pub unsafe fn use_backup(&self) {
        let cpu_id = cpu::cpu_id();
        let mask = !(1 << cpu_id);
        self.flags.fetch_and(mask, Ordering::Relaxed);
    }

    /// switch to primary allocator
    pub unsafe fn use_primary(&self) {
        let cpu_id = cpu::cpu_id();
        let mask = 1 << cpu_id;
        self.flags.fetch_or(mask, Ordering::Relaxed);
    }

    pub unsafe fn save<'a>(&'a self) -> Guard<'a> {
        let cpu_id = cpu::cpu_id();
        let mask = 1 << cpu_id;
        let flag = mask & self.flags.load(Ordering::Relaxed);
        Guard { talloc: self, flag }
    }

    pub unsafe fn restore(&self, flag: u64) {
        self.flags.fetch_or(flag, Ordering::Relaxed);
    }

    /// check whether using the primary allocator
    pub unsafe fn is_primary(&self) -> bool {
        let cpu_id = cpu::cpu_id();
        let val = self.flags.load(Ordering::Relaxed);
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

    pub unsafe fn init(&self, heap_start: usize, heap_size: usize) {
        let mut node = MCSNode::new();
        let mut guard = self.0.lock(&mut node);
        init_heap(&mut guard, heap_start, heap_size);
    }
}

impl BackUpAllocator {
    pub const fn new() -> Self {
        Self(MCSLock::new(Tlsf::new()))
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
