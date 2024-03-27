//! # Autoware Kernel
//!
//! Autoware kernel is a safe and realtime operating system.
//! It can execute async/await applications in kernel space safely.

#![feature(start)]
#![feature(abi_x86_interrupt)]
#![feature(allocator_api)]
#![no_main]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use awkernel_async_lib::{
    scheduler::{wake_task, SchedulerType},
    task,
};
use core::{
    fmt::Debug,
    sync::atomic::{AtomicBool, Ordering},
};
use kernel_info::KernelInfo;

mod arch;
mod config;
mod kernel_info;

#[cfg(not(feature = "std"))]
mod nostd;

static PRIMARY_READY: AtomicBool = AtomicBool::new(false);

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
        #[cfg(not(feature = "std"))]
        if let Some(irq) = awkernel_lib::timer::irq_id() {
            use alloc::boxed::Box;

            awkernel_lib::interrupt::enable_irq(irq);

            let timer_callback = Box::new(|_irq| {
                awkernel_lib::timer::reset();
            });

            if awkernel_lib::interrupt::register_handler(irq, "local timer".into(), timer_callback)
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

        PRIMARY_READY.store(true, Ordering::SeqCst);

        loop {
            awkernel_lib::interrupt::disable();

            wake_task(); // Wake executable tasks periodically.
            awkernel_lib::net::poll(); // Poll network devices.

            awkernel_lib::interrupt::enable();

            #[cfg(feature = "std")]
            awkernel_lib::delay::wait_microsec(50);

            #[cfg(not(feature = "std"))]
            {
                if awkernel_lib::timer::is_timer_enabled() {
                    let _int_guard = awkernel_lib::interrupt::InterruptGuard::new();
                    awkernel_lib::interrupt::enable();
                    awkernel_lib::timer::reset();
                    awkernel_lib::delay::wait_interrupt();
                    awkernel_lib::interrupt::disable();
                } else {
                    awkernel_lib::delay::wait_microsec(10);
                }
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
    }

    // Non-primary CPUs.
    #[cfg(not(feature = "std"))]
    {
        while !PRIMARY_READY.load(Ordering::SeqCst) {
            awkernel_lib::delay::wait_microsec(10);
        }

        awkernel_lib::interrupt::enable_irq(config::PREEMPT_IRQ);

        if let Some(irq) = awkernel_lib::timer::irq_id() {
            awkernel_lib::interrupt::enable_irq(irq);
        }
    }

    unsafe { task::run() }; // Execute tasks.
}
