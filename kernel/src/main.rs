//! # Autoware Kernel
//!
//! Autoware Kernel is a safe and realtime operating system
//! supporting isolated zero-copy communications written in Rust.

#![feature(lang_items)]
#![feature(start)]
#![feature(abi_x86_interrupt)]
#![no_main]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use awkernel_async_lib::{
    scheduler::{wake_task, SchedulerType},
    task,
};
use awkernel_lib::delay::pause;
use core::fmt::Debug;
use kernel_info::KernelInfo;

mod arch;
mod config;
mod kernel_info;

#[cfg(not(feature = "std"))]
mod nostd;

/// `main` function is called from each CPU.
/// `kernel_info.cpu_id` represents the CPU identifier.
/// The primary CPU's identifier is 0.
///
/// `Info` of `KernelInfo<Info>` represents architecture specific information.
fn main<Info: Debug>(kernel_info: KernelInfo<Info>) {
    log::info!("CPU#{} is starting.", kernel_info.cpu_id);

    // TODO: currently interrupt is supported for only AArch64
    #[cfg(all(feature = "aarch64", not(feature = "std")))]
    awkernel_lib::interrupt::enable();

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
