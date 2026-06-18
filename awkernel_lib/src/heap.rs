//! Heap memory allocator.
//!
//! The heap backend is selected by compile-time feature flags.
//!
//! - `heap-wf-alloc` enables the `wf_alloc` backend (supported on `x86_64` /
//!   `aarch64`).
//! - when `heap-wf-alloc` is not enabled, TLSF is used.
//!
//! In practice, binaries choose one of these paths via their feature set
//! (`kernel` enables `heap-wf-alloc` on x86 by default, while `heap-tlsf`
//! is used for non-`x86_64`/`aarch64` targets).
//!
//! # TLSF Backend
//!
//! `FLLEN` is the number of first-level list buckets and `SLLEN` is the number
//! of second-level list buckets.
//!
//! `minimum_size = size_of::<usize>() * 4`
//!
//! For example, on a 64-bit system, the minimum block size is `minimum_size = size_of::<usize>() * 4 = 32` bytes,
//! while the maximum block size is `(32 << FLLEN) - 1`.
//! The maximum size requested  should be smaller than this.
//! The worst-case internal fragmentation is `(32 << FLLEN) / SLLEN - 2` bytes.
//!
//! # wf_alloc Backend
//!
//! `wf_alloc` initializes `WfSpanAllocator` from the raw heap region:
//! 1. Align `heap_start` by `metadata_region_align()`.
//! 2. Reserve `metadata_region_size(active_threads)` bytes for metadata.
//! 3. Align the remaining start by `wf_alloc::SPAN_ALIGN`.
//! 4. Construct the allocator with `from_metadata_region(...)` and initialize it with `init(...)`.
//!
//! CPU IDs are mapped directly to `wf_alloc` tokens, so allocation/deallocation
//! is done with `InterruptGuard` and `alloc_with_token` / `dealloc_with_token`.
//!
//! If `wf_alloc` cannot be initialized, its allocator stays uninitialized and
//! every allocation returns `null`. There is no graceful, `alloc_error_handler`-style
//! recovery: when `Talloc::alloc` observes the `null`, the primary path calls
//! `panic!()`, and the non-primary path prints an error via `unsafe_puts` and then
//! halts in `delay::wait_forever()`. In other words, a failed `wf_alloc`
//! initialization means the kernel does not boot (or every userland allocation
//! panics), rather than falling back to some other OOM behavior.
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

#[cfg(not(all(
    feature = "heap-wf-alloc",
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
const FLLEN: usize = 28; // The maximum block size is (32 << 28) - 1 = 8_589_934_591 (nearly 8GiB)
#[cfg(not(all(
    feature = "heap-wf-alloc",
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
const SLLEN: usize = 64; // The worst-case internal fragmentation is ((32 << 28) / 64 - 2) = 134_217_726 (nearly 128MiB)
#[cfg(not(all(
    feature = "heap-wf-alloc",
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
type FLBitmap = u32; // must be longer than FLLEN
#[cfg(not(all(
    feature = "heap-wf-alloc",
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
type SLBitmap = u64; // must be longer than SLLEN

use crate::{
    console::{unsafe_print_hex_u64, unsafe_puts},
    cpu::{self, NUM_MAX_CPU},
    delay,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    mem::transmute,
    sync::atomic::{AtomicU32, AtomicUsize, Ordering},
};

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
///
/// This wrapper reads the active CPU count internally via `cpu::num_cpu()`, so it
/// must only be called after that count has been established (i.e. after
/// `set_num_cpu()`). For the `wf_alloc` backend the count becomes the allocator's
/// `active_threads`; if `cpu::num_cpu()` returns `0` (for example on x86_64, where
/// the heap is initialized before `set_num_cpu()` runs), `WfAllocBackend::init`
/// silently bails out at its `active_threads == 0` check and the heap is left
/// uninitialized. Callers that initialize the heap before the CPU count is known
/// must use [`init_primary_with_num_cpu`] with an explicit count instead.
pub unsafe fn init_primary(primary_start: usize, primary_size: usize) {
    TALLOC.init_primary(primary_start, primary_size);
}

/// # Safety
///
/// This must be called at initialization with the number of CPUs that can
/// concurrently use the heap.
pub unsafe fn init_primary_with_num_cpu(primary_start: usize, primary_size: usize, num_cpu: usize) {
    TALLOC.init_primary_with_num_cpu(primary_start, primary_size, num_cpu);
}

/// # Safety
///
/// This must be called at initialization.
///
/// This wrapper reads the active CPU count internally via `cpu::num_cpu()`, so it
/// must only be called after that count has been established (i.e. after
/// `set_num_cpu()`). For the `wf_alloc` backend the count becomes the allocator's
/// `active_threads`; if `cpu::num_cpu()` returns `0` (for example on x86_64, where
/// the heap is initialized before `set_num_cpu()` runs), `WfAllocBackend::init`
/// silently bails out at its `active_threads == 0` check and the heap is left
/// uninitialized. Callers that initialize the heap before the CPU count is known
/// must use [`init_backup_with_num_cpu`] with an explicit count instead.
pub unsafe fn init_backup(backup_start: usize, backup_size: usize) {
    TALLOC.init_backup(backup_start, backup_size);
}

/// # Safety
///
/// This must be called at initialization with the number of CPUs that can
/// concurrently use the heap.
pub unsafe fn init_backup_with_num_cpu(backup_start: usize, backup_size: usize, num_cpu: usize) {
    TALLOC.init_backup_with_num_cpu(backup_start, backup_size, num_cpu);
}

#[cfg(all(
    feature = "heap-wf-alloc",
    not(any(target_arch = "x86_64", target_arch = "aarch64"))
))]
compile_error!("heap-wf-alloc currently requires a wf_alloc CAS2 backend for this architecture");

#[cfg(all(
    feature = "heap-wf-alloc",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
type Allocator = wf_alloc_backend::WfAllocBackend;

#[cfg(not(all(
    feature = "heap-wf-alloc",
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
type Allocator = tlsf_backend::TlsfBackend;

trait HeapBackend {
    unsafe fn init(&self, heap_start: usize, heap_size: usize, active_threads: usize);

    unsafe fn alloc(&self, layout: Layout) -> *mut u8;

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout);
}

pub struct Talloc {
    primary: Allocator,
    backup: Allocator,

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
            let ptr = unsafe { self.primary.alloc(layout) };
            if ptr.is_null() {
                panic!();
            } else {
                ptr
            }
        } else {
            let ptr = unsafe { self.primary.alloc(layout) };
            if !ptr.is_null() {
                return ptr;
            }

            let ptr = unsafe { self.backup.alloc(layout) };
            if ptr.is_null() {
                unsafe_puts("failed to allocate heap memory\r\n");
                unsafe_puts("aborting...\r\n");
                delay::wait_forever();
            }
            ptr
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if self.is_primary_mem(ptr) {
            unsafe { self.primary.dealloc(ptr, layout) };
        } else {
            unsafe { self.backup.dealloc(ptr, layout) };
        }
    }
}

pub struct Guard<'a> {
    talloc: &'a Talloc,
    index: usize,
    flag: u32,
}

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        unsafe { self.talloc.restore(self.index, self.flag) };
    }
}

impl Default for Talloc {
    fn default() -> Self {
        Self::new()
    }
}

impl Talloc {
    pub const fn new() -> Self {
        let flags = [0; NUM_MAX_CPU / 32];

        Self {
            primary: Allocator::new(),
            backup: Allocator::new(),
            flags: unsafe {
                transmute::<
                    [i32; NUM_MAX_CPU / 32],
                    [core::sync::atomic::AtomicU32; NUM_MAX_CPU / 32],
                >(flags)
            },
            primary_start: AtomicUsize::new(0),
            primary_size: AtomicUsize::new(0),
            backup_start: AtomicUsize::new(0),
            backup_size: AtomicUsize::new(0),
        }
    }

    pub fn init_primary(&self, primary_start: usize, primary_size: usize) {
        self.init_primary_with_num_cpu(primary_start, primary_size, cpu::num_cpu());
    }

    pub fn init_primary_with_num_cpu(
        &self,
        primary_start: usize,
        primary_size: usize,
        num_cpu: usize,
    ) {
        self.primary_start.store(primary_start, Ordering::Relaxed);
        self.primary_size.store(primary_size, Ordering::Relaxed);

        unsafe { self.primary.init(primary_start, primary_size, num_cpu) };
    }

    pub fn init_backup(&self, backup_start: usize, backup_size: usize) {
        self.init_backup_with_num_cpu(backup_start, backup_size, cpu::num_cpu());
    }

    pub fn init_backup_with_num_cpu(
        &self,
        backup_start: usize,
        backup_size: usize,
        num_cpu: usize,
    ) {
        self.backup_start.store(backup_start, Ordering::Relaxed);
        self.backup_size.store(backup_size, Ordering::Relaxed);

        unsafe { self.backup.init(backup_start, backup_size, num_cpu) };
    }

    #[inline(always)]
    fn cpu_index() -> (usize, u32) {
        let cpu_id = cpu::cpu_id();
        let index = cpu_id >> 5;
        let id = cpu_id & (32 - 1);
        (index, id as u32)
    }

    #[inline(always)]
    fn cpu_index_cpu_id(cpu_id: usize) -> (usize, u32) {
        let index = cpu_id >> 5;
        let id = cpu_id & (32 - 1);
        (index, id as u32)
    }

    /// use both the primary and backup allocators
    /// # Safety
    ///
    /// After calling this function, the heap memory allocator uses both the primary and backup allocators.
    #[inline]
    pub unsafe fn use_primary_then_backup(&self) {
        let (index, cpu_id) = Self::cpu_index();
        let mask = !(1 << cpu_id);
        self.flags[index].fetch_and(mask, Ordering::Relaxed);
    }

    /// use both the primary and backup allocators
    /// # Safety
    ///
    /// After calling this function, the heap memory allocator uses both the primary and backup allocators.
    #[inline]
    pub unsafe fn use_primary_then_backup_cpu_id(&self, cpu_id: usize) {
        let (index, cpu_id) = Self::cpu_index_cpu_id(cpu_id);
        let mask = !(1 << cpu_id);
        self.flags[index].fetch_and(mask, Ordering::Relaxed);
    }

    /// use only the primary allocator
    ///
    /// # Safety
    ///
    /// After calling this function, the heap memory allocator uses only the primary allocator.
    #[inline]
    pub unsafe fn use_primary(&self) {
        let (index, cpu_id) = Self::cpu_index();
        let mask = 1 << cpu_id;
        self.flags[index].fetch_or(mask, Ordering::Relaxed);
    }

    /// use only the primary allocator
    ///
    /// # Safety
    ///
    /// After calling this function, the heap memory allocator uses only the primary allocator.
    #[inline]
    pub unsafe fn use_primary_cpu_id(&self, cpu_id: usize) {
        let (index, cpu_id) = Self::cpu_index_cpu_id(cpu_id);
        let mask = 1 << cpu_id;
        self.flags[index].fetch_or(mask, Ordering::Relaxed);
    }

    /// Save the configuration and it will be restored when dropping `Guard`.
    #[inline]
    pub fn save(&self) -> Guard<'_> {
        let (index, cpu_id) = Self::cpu_index();
        let mask = 1 << cpu_id;
        let flag = mask & self.flags[index].load(Ordering::Relaxed);
        Guard {
            talloc: self,
            index,
            flag,
        }
    }

    #[inline]
    unsafe fn restore(&self, index: usize, flag: u32) {
        self.flags[index].fetch_or(flag, Ordering::Relaxed);
    }

    /// check whether using the primary allocator
    #[inline]
    pub fn is_primary(&self) -> bool {
        let (index, cpu_id) = Self::cpu_index();
        let val = self.flags[index].load(Ordering::Relaxed);
        (val & (1 << cpu_id)) != 0
    }

    #[inline]
    pub fn is_primary_mem(&self, ptr: *mut u8) -> bool {
        let addr = ptr as usize;
        let start = self.primary_start.load(Ordering::Relaxed);
        let end = start + self.primary_size.load(Ordering::Relaxed);

        (start..end).contains(&addr)
    }
}

#[cfg(not(all(
    feature = "heap-wf-alloc",
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
mod tlsf_backend {
    use super::{FLBitmap, HeapBackend, Layout, SLBitmap, FLLEN, SLLEN};
    use crate::sync::{mcs::MCSNode, mutex::Mutex};
    use core::{ptr, ptr::NonNull};
    use rlsf::Tlsf;

    type TLSFAlloc = Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>;

    pub struct TlsfBackend(Mutex<TLSFAlloc>);

    impl TlsfBackend {
        pub const fn new() -> Self {
            Self(Mutex::new(Tlsf::new()))
        }
    }

    impl HeapBackend for TlsfBackend {
        unsafe fn init(&self, heap_start: usize, heap_size: usize, _active_threads: usize) {
            let mut node = MCSNode::new();
            let mut guard = self.0.lock(&mut node);
            unsafe { init_heap(&mut guard, heap_start, heap_size) };
        }

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
            unsafe { guard.deallocate(NonNull::new_unchecked(ptr), layout.align()) };
        }
    }

    unsafe fn init_heap(allocator: &mut TLSFAlloc, heap_start: usize, heap_size: usize) {
        let heap_mem = unsafe { core::slice::from_raw_parts_mut(heap_start as *mut u8, heap_size) };
        let Some(heap_mem) = NonNull::new(heap_mem) else {
            return;
        };
        allocator.insert_free_block_ptr(heap_mem);
    }
}

#[cfg(all(
    feature = "heap-wf-alloc",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
mod wf_alloc_backend {
    use super::{
        cpu, delay, unsafe_print_hex_u64, unsafe_puts, HeapBackend, Layout, NUM_MAX_CPU,
    };
    use crate::interrupt::InterruptGuard;
    use core::{
        cell::UnsafeCell,
        mem::MaybeUninit,
        ptr,
        sync::atomic::{AtomicBool, Ordering},
    };
    use wf_alloc::WfSpanAllocator;

    type WfAlloc = WfSpanAllocator<{ wf_alloc::MAX_SUPPORTED_CLASSES }>;

    pub struct WfAllocBackend {
        state: UnsafeCell<MaybeUninit<WfAlloc>>,
        initialized: AtomicBool,
    }

    unsafe impl Sync for WfAllocBackend {}

    impl WfAllocBackend {
        pub const fn new() -> Self {
            Self {
                state: UnsafeCell::new(MaybeUninit::uninit()),
                initialized: AtomicBool::new(false),
            }
        }

        fn allocator(&self) -> Option<&WfAlloc> {
            if self.initialized.load(Ordering::Acquire) {
                Some(unsafe { (&*self.state.get()).assume_init_ref() })
            } else {
                None
            }
        }
    }

    impl HeapBackend for WfAllocBackend {
        unsafe fn init(&self, heap_start: usize, heap_size: usize, active_threads: usize) {
            if self.initialized.load(Ordering::Acquire) {
                return;
            }

            let Some(metadata_start) = align_up(heap_start, WfAlloc::metadata_region_align())
            else {
                return;
            };
            let Some(metadata_offset) = metadata_start.checked_sub(heap_start) else {
                return;
            };
            if metadata_offset >= heap_size {
                return;
            }

            if active_threads == 0 || active_threads > NUM_MAX_CPU {
                return;
            }

            let metadata_len = heap_size - metadata_offset;
            let Some(required_metadata_len) = WfAlloc::metadata_region_size(active_threads) else {
                return;
            };
            if required_metadata_len > metadata_len {
                return;
            }

            let Some(after_metadata) = metadata_start.checked_add(required_metadata_len) else {
                return;
            };
            let Some(region_start) = align_up(after_metadata, wf_alloc::SPAN_ALIGN) else {
                return;
            };
            let Some(region_offset) = region_start.checked_sub(heap_start) else {
                return;
            };
            if region_offset >= heap_size {
                return;
            }

            let region_len = heap_size - region_offset;
            if region_len < wf_alloc::SPAN_SIZE {
                return;
            }

            let Some((allocator, _metadata_used)) = (unsafe {
                WfAlloc::from_metadata_region(
                    active_threads,
                    metadata_start as *mut u8,
                    required_metadata_len,
                )
            }) else {
                return;
            };

            unsafe { (*self.state.get()).write(allocator) };
            let allocator = unsafe { (&*self.state.get()).assume_init_ref() };
            unsafe { allocator.init(region_start as *mut u8, region_len) };
            self.initialized.store(true, Ordering::Release);
        }

        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let Some(allocator) = self.allocator() else {
                return ptr::null_mut();
            };
            let _interrupt_guard = InterruptGuard::new();
            let cpu_id = cpu::cpu_id();
            if cpu_id >= allocator.active_threads() {
                return ptr::null_mut();
            }
            let token = unsafe { allocator.registry.token_from_raw(cpu_id) };
            unsafe { allocator.alloc_with_token(layout, token) }
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            let Some(allocator) = self.allocator() else {
                return;
            };
            let _interrupt_guard = InterruptGuard::new();
            let cpu_id = cpu::cpu_id();
            if cpu_id >= allocator.active_threads() {
                // A CPU outside the configured `active_threads` range is freeing a
                // block. Silently dropping it would permanently leak the block, so we
                // fail loudly. We halt instead of `panic!` because the panic handler
                // allocates, which would re-enter this same out-of-range guard on this
                // CPU.
                unsafe {
                    unsafe_puts("wf_alloc dealloc: cpu_id out of range (cpu_id=0x");
                    unsafe_print_hex_u64(cpu_id as u64);
                    unsafe_puts(", active_threads=0x");
                    unsafe_print_hex_u64(allocator.active_threads() as u64);
                    unsafe_puts(") -- heap misconfigured; aborting...\r\n");
                }
                delay::wait_forever();
            }
            let token = unsafe { allocator.registry.token_from_raw(cpu_id) };
            unsafe { allocator.dealloc_with_token(ptr, layout, token) };
        }
    }

    fn align_up(value: usize, align: usize) -> Option<usize> {
        debug_assert!(align.is_power_of_two());
        value
            .checked_add(align - 1)
            .map(|value| value & !(align - 1))
    }
}
