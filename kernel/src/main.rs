//! # T4 Operating System
//!
//! T4 Operating System (T4OS) is a safe and realtime operating system
//! supporting isolated zero-copy communications written in Rust.

#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(start)]
#![feature(abi_x86_interrupt)]
#![no_std]
#![no_main]

extern crate alloc;

use alloc::boxed::Box;
use core::{alloc::Layout, fmt::Debug};
use kernel_info::KernelInfo;
use t4os_async_lib::{
    scheduler::{wake_task, SchedulerType},
    task,
};
use t4os_lib::delay::{pause, wait_forever};

mod arch;
mod config;
mod heap;
mod kernel_info;

/// `main` function is called from each CPU.
/// `kernel_info.cpu_id` represents the CPU identifier.
/// The primary CPU's identifier is 0.
///
/// `Info` of `KernelInfo<Info>` represents architecture specific information.
fn main<Info: Debug>(kernel_info: KernelInfo<Info>) {
    log::info!("CPU#{} is starting.", kernel_info.cpu_id);

    if kernel_info.cpu_id == 0 {
        // Primary CPU.

        // Userland.
        task::spawn(
            async move { userland::main().await },
            SchedulerType::RoundRobin,
        );

        loop {
            wake_task(); // Wake executable tasks periodically.
            pause();
        }
    } else {
        // Non-primary CPUs.
        task::run(kernel_info.cpu_id); // Execute tasks.
    }
}

#[alloc_error_handler]
fn on_oom(_layout: Layout) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    wait_forever();
}

#[cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    not(feature = "linux")
))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    wait_forever();
}
