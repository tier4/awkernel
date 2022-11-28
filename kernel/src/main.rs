#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![no_std]
#![no_main]

extern crate alloc;
extern crate unwinding;

use alloc::boxed::Box;
use bootloader::{entry_point, BootInfo};
use core::{alloc::Layout, fmt::Write, panic::PanicInfo};

mod config;
mod heap;

mod x86_64;

entry_point!(kernel_main);

fn kernel_main(boot_info: &'static mut BootInfo) -> ! {
    let mut serial_port = unsafe { uart_16550::SerialPort::new(0x3F8) };
    serial_port.init();

    match heap::init(boot_info) {
        Ok(_) => {
            let _ = serial_port.write_str("Heap memory has been successfully initialized.\n");
        }
        Err(err) => {
            let _ = serial_port.write_fmt(format_args!(
                "Failed to initialize heap memory: reason = {:?}\n",
                err
            ));
            loop {}
        }
    }

    let mut serial_port = unsafe { uart_16550::SerialPort::new(0x3F8) };
    serial_port.init();
    serial_port.write_str("Hello, world!\n").unwrap();

    let n = Box::new(10); // Heap memory allocation

    if let Some(framebuffer) = boot_info.framebuffer.as_mut() {
        for byte in framebuffer.buffer_mut() {
            *byte = 0x90;
        }
    }

    loop {}
}

#[alloc_error_handler]
fn on_oom(layout: Layout) -> ! {
    unwinding::panic::begin_panic(Box::new(layout));
    loop {}
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
