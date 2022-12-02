#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(start)]
#![no_std]
#![no_main]
#![allow(dead_code)]

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

fn main<Info>(_board_info: &BoardInfo<Info>) {
    heap::init();
    let n = Box::new(10);

    log::debug!("{n}");
    log::debug!("Hello, world!");
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
