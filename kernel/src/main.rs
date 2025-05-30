//! # Awkernel
//!
//! Awkernel is a safe and realtime operating system.
//! It can execute async/await applications in kernel space safely.

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
    sync::atomic::{AtomicBool, AtomicU16, Ordering},
};
use kernel_info::KernelInfo;

mod arch;
mod config;
mod kernel_info;

#[cfg(not(feature = "std"))]
mod nostd;

static PRIMARY_READY: AtomicBool = AtomicBool::new(false);
static NUM_READY_WORKER: AtomicU16 = AtomicU16::new(0);

/// `main` function is called from each CPU.
/// `kernel_info.cpu_id` represents the CPU identifier.
/// The primary CPU's identifier is 0.
///
/// `Info` of `KernelInfo<Info>` represents architecture specific information.
fn main<Info: Debug>(kernel_info: KernelInfo<Info>) {
    log::info!("CPU#{} is starting.", kernel_info.cpu_id);

    if kernel_info.cpu_id == 0 {
        // Primary CPU.

        unsafe { awkernel_lib::cpu::set_num_cpu(kernel_info.num_cpu) };

        #[cfg(not(feature = "std"))]
        awkernel_lib::interrupt::set_preempt_irq(
            config::PREEMPT_IRQ,
            awkernel_async_lib::task::preemption,
        );

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

        // Wait until all other CPUs have incremented NUM_CPU
        while NUM_READY_WORKER.load(Ordering::SeqCst) < (kernel_info.num_cpu - 1) as u16 {
            awkernel_lib::delay::wait_microsec(10);
        }

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
        }
    }

    // Non-primary CPUs.
    while !PRIMARY_READY.load(Ordering::SeqCst) {
        awkernel_lib::delay::wait_microsec(10);
    }

    #[cfg(not(feature = "std"))]
    {
        awkernel_lib::interrupt::enable_irq(config::PREEMPT_IRQ);

        if let Some(irq) = awkernel_lib::timer::irq_id() {
            awkernel_lib::interrupt::enable_irq(irq);
        }
    }

    NUM_READY_WORKER.fetch_add(1, Ordering::Relaxed);

    unsafe { task::run() }; // Execute tasks.
}
