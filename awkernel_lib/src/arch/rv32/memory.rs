/// RV32 Memory Management Module
///
/// This module provides basic memory management functionality for RISC-V 32-bit systems.
/// The main memory management is handled by the vm.rs module, but this module provides
/// some basic constants and utilities that may be needed by other parts of the system.
use super::address::MEMORY_END;

/// Memory end address for RV32 systems
///
/// This constant defines the end of physical memory that can be used by the kernel.
/// It's set to 0x8800_0000 (approximately 2.125 GB) which is a reasonable limit
/// for 32-bit RISC-V systems.
pub const RV32_MEMORY_END: u64 = MEMORY_END;

/// Check if a physical address is within valid memory range
///
/// This function validates that a given physical address is within the addressable
/// memory range for RV32 systems.
#[allow(dead_code)]
pub fn is_valid_physical_address(addr: usize) -> bool {
    addr < (RV32_MEMORY_END as usize)
}

/// Get the maximum usable physical memory size
///
/// Returns the maximum amount of physical memory that can be used by the system.
#[allow(dead_code)]
pub fn max_physical_memory() -> usize {
    RV32_MEMORY_END as usize
}
