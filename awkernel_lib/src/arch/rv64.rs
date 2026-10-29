pub(super) mod address;
pub(super) mod dvfs;
pub(super) mod fdt;

use core::sync::atomic::{AtomicUsize, Ordering};

pub struct RV64;

impl super::Arch for RV64 {}

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
                crate::console::unsafe_print_hex_u32((dtb_addr >> 32) as u32);
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
                crate::console::unsafe_print_hex_u32((dtb_addr >> 32) as u32);
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

/// Get the memory end address based on detected memory size
///
/// This function attempts to detect the actual available RAM and returns
/// an appropriate MEMORY_END value. Panics if detection fails.
pub fn get_memory_end() -> u64 {
    const DRAM_BASE: u64 = 0x80000000;

    if let Some(detected_size) = detect_memory_size() {
        // Use detected size directly
        let memory_end = DRAM_BASE + detected_size;

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
        // Failed to detect memory - cannot continue boot safely
        panic!("Failed to detect memory size from DTB or probing - cannot boot");
    }
}

/// Detect CPU count from device tree
///
/// Returns the detected number of CPUs. Panics if detection fails.
pub fn detect_cpu_count() -> usize {
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

        // Failed to detect CPU count - cannot continue boot safely
        panic!("Failed to detect CPU count from DTB - cannot boot");
    }
}
