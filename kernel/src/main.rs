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
use core::{alloc::Layout, fmt::Debug};
use delay::Delay;
use kernel_info::KernelInfo;

mod arch;
mod config;
mod delay;
mod heap;
mod kernel_info;
mod logger;
mod mmio;
mod scheduler;
mod task;

fn main<Info: Debug>(kernel_info: KernelInfo<Info>) {
    log::info!("CPU#{} is starting.", kernel_info.cpu_id);

    if kernel_info.cpu_id == 0 {
        loop {
            delay::wait_microsec(1);
        }
    } else {
        // task::run();
        loop {
            delay::wait_millisec(1500);
            log::debug!("CPU#{}: tick", kernel_info.cpu_id);
        }
    }
}

#[alloc_error_handler]
fn on_oom(_layout: Layout) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    delay::ArchDelay::wait_forever();
}

#[cfg(any(feature = "x86", feature = "aarch64"))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    delay::ArchDelay::wait_forever();
}
