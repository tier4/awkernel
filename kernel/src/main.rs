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
    task, uptime,
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

    unsafe { awkernel_lib::cpu::increment_num_cpu() };

    if kernel_info.cpu_id == 0 {
        // Primary CPU.

        #[cfg(not(feature = "std"))]
        awkernel_lib::interrupt::set_preempt_irq(
            config::PREEMPT_IRQ,
            awkernel_async_lib::task::preemption,
        );

        // Userland.
        task::spawn(
            "main".into(),
            async move { userland::main().await },
            SchedulerType::RoundRobin,
        );

        #[cfg(feature = "aarch64")]
        let mut send_ipi = uptime();

        loop {
            wake_task(); // Wake executable tasks periodically.

            #[cfg(not(feature = "std"))]
            awkernel_lib::delay::wait_microsec(1);

            #[cfg(feature = "aarch64")]
            {
                let now = uptime();
                if now >= send_ipi {
                    if now - send_ipi >= 20_000 {
                        awkernel_lib::interrupt::send_ipi_broadcast_without_self(
                            config::PREEMPT_IRQ,
                        );
                        send_ipi = now;
                    }
                }
            }

            #[cfg(feature = "std")]
            awkernel_lib::delay::wait_microsec(10);
        }
    } else {
        #[cfg(not(feature = "std"))]
        {
            awkernel_lib::interrupt::enable_irq(config::PREEMPT_IRQ);
            awkernel_lib::interrupt::disable();
        }

        // Non-primary CPUs.
        unsafe { task::run() }; // Execute tasks.
    }
}
