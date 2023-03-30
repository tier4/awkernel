mod apic;
pub mod config;
mod heap;
mod interrupt;
mod kernel_main;
mod serial;
mod stack;

pub unsafe fn puts(data: &str) {
    serial::puts(data);
}
