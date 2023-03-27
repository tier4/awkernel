mod apic;
pub mod config;
pub mod cpu;
mod heap;
mod interrupt;
mod kernel_main;
mod page_allocator;
mod serial;
mod stack;

pub unsafe fn puts(data: &str) {
    serial::puts(data);
}
