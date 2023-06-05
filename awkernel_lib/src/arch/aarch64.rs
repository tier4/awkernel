pub mod arm_timer;
pub mod context;
pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod interrupt;
pub(super) mod memory;
pub mod page_allocator;
pub mod page_table;
pub mod rpi_system_timer;

pub unsafe fn init_primary() {
    delay::init_primary();
}

pub unsafe fn init_non_primary() {
    delay::init_non_primary();
}

pub use cpu::set_cluster_info;
