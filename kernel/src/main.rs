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

    if kernel_info.cpu_id == 0 {
        // Primary CPU.

        // TODO: currently interrupt and timer is supported for only AArch64
        #[cfg(feature = "aarch64")]
        {
            let irq = awkernel_lib::timer::irq_id().unwrap();
            awkernel_lib::interrupt::enable_irq(irq);
            awkernel_lib::interrupt::register_handler(irq, || {
                awkernel_lib::timer::reset();
            })
            .unwrap();

            awkernel_lib::timer::reset();
            awkernel_lib::interrupt::enable();
        }

        // Userland.
        task::spawn(
            async move { userland::main().await },
            SchedulerType::RoundRobin,
        );

        loop {
            wake_task(); // Wake executable tasks periodically.

            #[cfg(not(feature = "std"))]
            {
                awkernel_lib::delay::wait_microsec(1);
            }

            #[cfg(feature = "std")]
            {
                awkernel_lib::delay::wait_microsec(10);
            }
        }
    } else {
        // Non-primary CPUs.
        unsafe { task::run(kernel_info.cpu_id) }; // Execute tasks.
    }
}
