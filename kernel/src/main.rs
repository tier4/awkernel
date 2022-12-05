#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(start)]
#![feature(abi_x86_interrupt)]
#![no_std]
#![no_main]
#![allow(dead_code)]

extern crate alloc;
extern crate unwinding;

use alloc::boxed::Box;
use arch::Delay;
use board_info::BoardInfo;
use core::{alloc::Layout, fmt::Debug};

mod arch;
mod board_info;
mod config;
mod heap;
mod logger;
mod mmio;

fn foo() {
    panic!("panic");
}

fn main<Info: Debug>(board_info: &BoardInfo<Info>) {
    heap::init();
    let n = Box::new(10);

    log::debug!("{n}");
    log::debug!("board_info: {:?}", board_info);

    match unwinding::panic::catch_unwind(|| {
        foo();
        log::debug!("finished");
    }) {
        Ok(_) => log::debug!("not caught panic"),
        Err(_) => log::debug!("caught panic"),
    }
}

#[alloc_error_handler]
fn on_oom(_layout: Layout) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    arch::ArchDelay::wait_forever();
}

#[cfg(not(feature = "linux"))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    log::debug!("panic(): 0");
    let reason = unwinding::panic::begin_panic(Box::new(()));
    log::debug!("panic(): {}", reason.0);
    arch::ArchDelay::wait_forever();
}
