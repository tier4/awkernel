pub mod context;
pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod interrupt;
pub mod page_allocator;
pub mod page_table;

pub unsafe fn init_primary() {
    delay::init_primary();
}

pub unsafe fn init_non_primary() {
    delay::init_non_primary();
}

pub use cpu::set_cluster_info;
