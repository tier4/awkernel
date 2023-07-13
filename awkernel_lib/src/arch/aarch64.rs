pub mod armv8_timer;
pub(super) mod cpu;
pub(super) mod delay;
pub mod exception_saved_regs;
pub(super) mod interrupt;
pub(super) mod memory;
pub mod page_allocator;
pub mod page_table;
pub mod rpi_system_timer;

/// # Safety
///
/// This function must be called at initialization,
/// and called the primary CPU.
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

pub use cpu::set_cluster_info;
