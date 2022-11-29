#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![no_std]
#![no_main]

extern crate alloc;
extern crate unwinding;

use alloc::boxed::Box;
use board_info::BoardInfo;
use core::{alloc::Layout, panic::PanicInfo};

mod arch;
mod board_info;
mod config;
mod heap;
mod mmio;

fn main<Info>(board_info: &BoardInfo<Info>) {
    heap::init();
    let _n = Box::new(10);

    log::info!("Hello, world!");
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
