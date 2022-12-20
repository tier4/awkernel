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
use core::{alloc::Layout, fmt::Debug};
use kernel_info::KernelInfo;

mod arch;
mod config;
mod heap;
mod kernel_info;
mod logger;
mod mmio;

fn foo() {
    panic!("panic");
}

fn main<Info: Debug>(kernel_info: KernelInfo<Info>) {
    if kernel_info.cpu_id == 0 {
        log::debug!("I am the primary CPU.");

        let n = Box::new(10);

        log::debug!("{n}");
        log::debug!("kernel_info: {:?}", kernel_info);

        match unwinding::panic::catch_unwind(|| {
            foo();
            log::debug!("finished");
        }) {
            Ok(_) => log::debug!("not caught panic"),
            Err(_) => log::debug!("caught panic"),
        }
    } else {
        log::debug!("I am a non primary CPU (#{}).", kernel_info.cpu_id);
    }
}

#[alloc_error_handler]
fn on_oom(_layout: Layout) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    arch::ArchDelay::wait_forever();
}

#[cfg(any(feature = "x86", feature = "aarch64"))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    arch::ArchDelay::wait_forever();
}
