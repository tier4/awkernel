//! # T4 Operating System
//!
//! T4 Operating System (T4OS) is a safe and realtime operating system
//! supporting isolated zero-copy communications written in Rust.

#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(start)]
#![feature(atomic_bool_fetch_not)]
#![feature(core_intrinsics)]
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
mod heap;

#[cfg(not(feature = "std"))]
mod nostd;

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
