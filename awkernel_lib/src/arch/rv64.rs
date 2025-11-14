pub(super) mod address;
pub mod barrier;
pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod dvfs;
pub(super) mod fdt;
pub(super) mod frame_allocator;
pub(super) mod interrupt;
pub(super) mod page_table;
pub(super) mod paging;
pub(super) mod vm;

use core::sync::atomic::{AtomicUsize, Ordering};

pub struct RV64;

impl super::Arch for RV64 {}

/// # Safety
///
/// This function must be called at initialization,
/// and called by the primary CPU.
pub unsafe fn init_primary() {
    delay::init_primary();
}

/// # Safety
///
/// This function must be called at initialization,
/// and called by non-primary CPUs.
pub unsafe fn init_non_primary() {
    delay::init_non_primary();
}

pub fn init_page_allocator() {
    frame_allocator::init_page_allocator();
}

pub fn init_kernel_space() {
    vm::init_kernel_space();
}

pub fn activate_kernel_space() {
    vm::activate_kernel_space();
}

pub fn get_kernel_token() -> usize {
    vm::kernel_token()
}

pub fn translate_kernel_address(vpn: address::VirtPageNum) -> Option<page_table::PageTableEntry> {
    use crate::sync::mcs::MCSNode;
    let mut node = MCSNode::new();
    let mut kernel_space = vm::KERNEL_SPACE.lock(&mut node);
    if let Some(ref mut space) = *kernel_space {
        space.translate(vpn)
    } else {
        None
    }
}

pub fn get_heap_size() -> usize {
    vm::get_heap_size()
}

static BOOT_DTB_PTR: AtomicUsize = AtomicUsize::new(0);

/// Record the DTB pointer supplied by firmware/bootloader.
pub fn set_boot_dtb_ptr(addr: usize) {
    BOOT_DTB_PTR.store(addr, Ordering::Relaxed);
}

fn boot_dtb_ptr() -> Option<usize> {
    match BOOT_DTB_PTR.load(Ordering::Relaxed) {
        0 => None,
        addr => Some(addr),
    }
}

/// Detect memory size from device tree or by probing
///
/// Returns the detected memory size in bytes, or None if detection fails
pub fn detect_memory_size() -> Option<u64> {
    unsafe {
        if let Some(dtb_addr) = boot_dtb_ptr() {
            if let Some(region) = fdt::detect_memory_from_dtb(dtb_addr) {
                unsafe_puts("Memory detected from boot DTB pointer at 0x");
                crate::console::unsafe_print_hex_u32((dtb_addr >> 16) as u32);
                crate::console::unsafe_print_hex_u32(dtb_addr as u32);
                unsafe_puts("\r\n");
                return Some(region.size);
            } else {
                unsafe_puts("Boot DTB pointer invalid, falling back to probe\r\n");
            }
        }

        // First, try to find DTB at common locations
        if let Some(dtb_addr) = fdt::probe_dtb_locations() {
            if let Some(region) = fdt::detect_memory_from_dtb(dtb_addr) {
                unsafe_puts("Memory detected from DTB at 0x");
                crate::console::unsafe_print_hex_u32((dtb_addr >> 16) as u32);
                crate::console::unsafe_print_hex_u32(dtb_addr as u32);
                unsafe_puts("\r\n");
                return Some(region.size);
            }
        }

        // Fallback: Try memory probing
        if let Some(size) = fdt::probe_memory_size() {
            use crate::console::unsafe_puts;
            unsafe_puts("Memory detected by probing\r\n");
            return Some(size);
        }
    }
    None
}

use crate::console::unsafe_puts;

/// Get the memory end address based on detected or default memory size
///
/// This function attempts to detect the actual available RAM and returns
/// an appropriate MEMORY_END value. Falls back to a safe default if detection fails.
pub fn get_memory_end() -> u64 {
    const DEFAULT_MEMORY_END: u64 = 0xB0000000; // 768MB default
    const DRAM_BASE: u64 = 0x80000000;

    if let Some(detected_size) = detect_memory_size() {
        // Use detected size, but cap it at reasonable limits
        let max_memory_end = DRAM_BASE + detected_size;

        // Don't exceed 2GB to be safe
        let memory_end = max_memory_end.min(DRAM_BASE + 0x80000000);

        // Log the detection
        unsafe {
            use crate::console::unsafe_puts;
            unsafe_puts("Detected RAM size: 0x");
            crate::console::unsafe_print_hex_u32((detected_size >> 32) as u32);
            crate::console::unsafe_print_hex_u32(detected_size as u32);
            unsafe_puts("\r\n");
        }

        memory_end
    } else {
        // Fall back to default
        unsafe {
            use crate::console::unsafe_puts;
            unsafe_puts("Using default MEMORY_END (DTB not found)\r\n");
        }
        DEFAULT_MEMORY_END
    }
}

/// Detect CPU count from device tree or return default
///
/// Returns the detected number of CPUs, or a safe default if detection fails
pub fn detect_cpu_count() -> usize {
    const DEFAULT_CPU_COUNT: usize = 4;

    unsafe {
        if let Some(dtb_addr) = boot_dtb_ptr() {
            if let Some(count) = fdt::detect_cpu_count_from_dtb(dtb_addr) {
                unsafe_puts("Detected ");
                crate::console::unsafe_print_hex_u32(count as u32);
                unsafe_puts(" CPUs from boot DTB\r\n");
                return count;
            }
        }

        // Try to find DTB at common locations
        if let Some(dtb_addr) = fdt::probe_dtb_locations() {
            if let Some(count) = fdt::detect_cpu_count_from_dtb(dtb_addr) {
                unsafe_puts("Detected ");
                crate::console::unsafe_print_hex_u32(count as u32);
                unsafe_puts(" CPUs from probed DTB\r\n");
                return count;
            }
        }

        // Fall back to default
        unsafe_puts("Using default CPU count\r\n");
        DEFAULT_CPU_COUNT
    }
}
