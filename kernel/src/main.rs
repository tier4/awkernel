#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![no_std]
#![no_main]

extern crate alloc;
extern crate unwinding;

use alloc::boxed::Box;
use board_info::BoardInfo;
use core::{alloc::Layout, fmt::Write, panic::PanicInfo};

mod board_info;
mod config;
mod heap;

mod arch;

fn main<Info, HeapInit>(board_info: &BoardInfo<Info>)
where
    HeapInit: heap::HeapInit<Info>,
{
    let mut serial_port = unsafe { uart_16550::SerialPort::new(0x3F8) };
    serial_port.init();

    match heap::init::<_, HeapInit>(board_info) {
        Ok(_) => {
            let _ = serial_port.write_str("Heap memory has been successfully initialized.\n");
        }
        Err(err) => {
            let _ = serial_port.write_fmt(format_args!(
                "Failed to initialize heap memory: reason = {:?}\n",
                err
            ));
            return;
        }
    }

    let _n = Box::new(10);

    serial_port.write_str("Hello, world!\n").unwrap();
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
