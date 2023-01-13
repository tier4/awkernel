use self::driver::uart::UART;

mod bsp;
pub mod config;
mod context;
mod cpu;
// pub mod delay;
mod driver;
mod exception;
mod kernel_main;
mod mmu;
mod serial;

pub unsafe fn puts(data: &str) {
    driver::uart::DevUART::unsafe_puts(data);
}
