//! # Autoware Kernel
//!
//! Autoware Kernel is a safe and realtime operating system
//! supporting isolated zero-copy communications written in Rust.

#![feature(start)]
#![feature(abi_x86_interrupt)]
#![feature(allocator_api)]
#![no_main]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use alloc::boxed::Box;
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

    unsafe { awkernel_lib::cpu::increment_num_cpu() };

    if kernel_info.cpu_id == 0 {
        // Primary CPU.

        #[cfg(not(feature = "std"))]
        awkernel_lib::interrupt::set_preempt_irq(
            config::PREEMPT_IRQ,
            awkernel_async_lib::task::preemption,
        );

        // Test for IPI.
        #[cfg(all(any(feature = "aarch64", feature = "x86"), not(feature = "std")))]
        let mut send_ipi = awkernel_lib::delay::uptime();

        // Set-up timer interrupt.
        if let Some(irq) = awkernel_lib::timer::irq_id() {
            awkernel_lib::interrupt::enable_irq(irq);

            if awkernel_lib::interrupt::register_handler(irq, Box::new(awkernel_lib::timer::reset))
                .is_ok()
            {
                log::info!("A local timer has been initialized.");
            }
        }

        awkernel_lib::sanity::check();

        // Userland.
        task::spawn(
            "main".into(),
            async move { userland::main().await },
            SchedulerType::FIFO,
        );

        loop {
            wake_task(); // Wake executable tasks periodically.

            #[cfg(not(all(feature = "aarch64", not(feature = "std"))))]
            awkernel_lib::delay::wait_microsec(10);

            // TODO: enable timer on x86.
            #[cfg(all(feature = "aarch64", not(feature = "std")))]
            {
                let _int_guard = awkernel_lib::interrupt::InterruptGuard::new();
                awkernel_lib::interrupt::enable();
                awkernel_lib::timer::reset();
                awkernel_lib::delay::wait_interrupt();
                awkernel_lib::timer::disable();
            }

            // Test for IPI.
            #[cfg(all(any(feature = "aarch64", feature = "x86"), not(feature = "std")))]
            {
                let now = awkernel_lib::delay::uptime();
                if now >= send_ipi {
                    let dur = 20_000; // 20[ms]
                    if now - send_ipi >= dur {
                        // Send IPI to all CPUs except for primary CPU.
                        awkernel_lib::interrupt::send_ipi_broadcast_without_self(
                            config::PREEMPT_IRQ,
                        );

                        send_ipi = now;
                    }
                }
            }
        }
    } else {
        awkernel_lib::interrupt::enable_irq(config::PREEMPT_IRQ);

        // Non-primary CPUs.
        unsafe { task::run() }; // Execute tasks.
    }
}
