//! Simple Flattened Device Tree (FDT) helpers for memory detection
//!
//! This module now leverages the `fdt` crate to extract memory information
//! while keeping a small, RV64-centric surface for the rest of the kernel.

use fdt::Fdt;

/// FDT Magic number (0xd00dfeed in big-endian)
const FDT_MAGIC: u32 = 0xd00dfeed;

const RISCV_DRAM_BASE: u64 = 0x8000_0000;
const RISCV_DRAM_MAX_BASE: u64 = 0x9000_0000;
const MAX_REASONABLE_REGION_SIZE: u64 = 0x1_0000_0000; // 4GB

/// Convert big-endian u32 to native endian
#[inline]
fn be32_to_cpu(val: u32) -> u32 {
    u32::from_be(val)
}

/// Memory region information
#[derive(Debug, Clone, Copy)]
pub struct MemoryRegion {
    pub base: u64,
    pub size: u64,
}

/// Detect memory size from device tree blob
///
/// # Safety
///
/// This function reads from the DTB address which must point to valid memory.
pub unsafe fn detect_memory_from_dtb(dtb_addr: usize) -> Option<MemoryRegion> {
    // Check if DTB address looks valid (aligned and non-zero)
    if dtb_addr == 0 || dtb_addr & 0x3 != 0 {
        return None;
    }

    let fdt = unsafe { Fdt::from_ptr(dtb_addr as *const u8).ok()? };
    let memory = fdt.memory();
    let mut regions = memory.regions().filter_map(convert_region);

    regions.find(is_reasonable_region)
}

fn convert_region(region: fdt::standard_nodes::MemoryRegion) -> Option<MemoryRegion> {
    let size = region.size? as u64;
    if size == 0 {
        return None;
    }

    Some(MemoryRegion {
        base: region.starting_address as usize as u64,
        size,
    })
}

fn is_reasonable_region(region: &MemoryRegion) -> bool {
    region.base >= RISCV_DRAM_BASE
        && region.base < RISCV_DRAM_MAX_BASE
        && region.size > 0
        && region.size < MAX_REASONABLE_REGION_SIZE
}

/// Probe common DTB locations used by QEMU and firmware
pub unsafe fn probe_dtb_locations() -> Option<usize> {
    // Common DTB locations for RISC-V:
    // 1. 0x82000000 - QEMU often places DTB here
    // 2. 0x88000000 - Alternative location
    // 3. 0x87000000 - Another common location
    // 4. 0xBFE00000 - End of 1GB RAM (QEMU default for some modes)

    let locations = [
        0xBFE00000, // Try end of 1GB first (QEMU -bios none)
        0x82000000, 0x88000000, 0x87000000, 0xBFF00000, // Alternative end location
    ];

    for &addr in &locations {
        // Check if this looks like a valid DTB
        let magic_ptr = addr as *const u32;
        if let Some(magic) = unsafe { magic_ptr.as_ref() } {
            if be32_to_cpu(*magic) == FDT_MAGIC {
                return Some(addr);
            }
        }
    }

    None
}

/// Probe available memory by checking if addresses are accessible
///
/// This is a fallback when DTB is not available. We probe memory
/// in chunks to find where RAM ends.
pub unsafe fn probe_memory_size() -> Option<u64> {
    const DRAM_BASE: usize = 0x80000000;
    const PROBE_STEP: usize = 64 * 1024 * 1024; // 64MB chunks
    const MAX_PROBE: usize = 2 * 1024 * 1024 * 1024; // Don't probe beyond 2GB

    let mut current = DRAM_BASE + PROBE_STEP;
    let mut last_valid = DRAM_BASE;

    while current < DRAM_BASE + MAX_PROBE {
        // Try to read from this address
        // If it causes an exception, the trap handler will catch it
        let test_addr = current as *const u32;

        // Simple heuristic: if we can read all zeros or all ones, likely not valid RAM
        if let Some(value) = test_addr.as_ref() {
            let val = *value;
            // Valid RAM typically has some non-uniform pattern
            // This is heuristic but better than crashing
            if val != 0xFFFFFFFF && val != 0x00000000 {
                last_valid = current;
            } else {
                // Might be end of RAM
                break;
            }
        } else {
            break;
        }

        current += PROBE_STEP;
    }

    if last_valid > DRAM_BASE {
        Some((last_valid - DRAM_BASE) as u64)
    } else {
        None
    }
}

/// Detect the number of CPUs from the device tree blob
///
/// # Safety
///
/// This function reads from the DTB address which must point to valid memory.
pub unsafe fn detect_cpu_count_from_dtb(dtb_addr: usize) -> Option<usize> {
    // Check if DTB address looks valid (aligned and non-zero)
    if dtb_addr == 0 || dtb_addr & 0x3 != 0 {
        return None;
    }

    let fdt = unsafe { Fdt::from_ptr(dtb_addr as *const u8).ok()? };

    // Count CPUs by iterating through /cpus node
    let cpu_count = fdt.cpus().count();

    if cpu_count > 0 {
        Some(cpu_count)
    } else {
        None
    }
}
