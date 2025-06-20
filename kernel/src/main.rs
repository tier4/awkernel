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
    #[cfg(feature = "perf")]
    awkernel_async_lib::task::perf::start_kernel();

    log::info!("CPU#{} is starting.", kernel_info.cpu_id);

    if kernel_info.cpu_id == 0 {
        // Primary CPU.

        #[cfg(feature = "std")]
        if make_stdin_nonblocking().is_err() {
            log::warn!("failed to make stdin non-blocking.");
        }

        unsafe { awkernel_lib::cpu::set_num_cpu(kernel_info.num_cpu) };

        // Initialize interrupts.
        #[cfg(not(feature = "std"))]
        init_interrupt();

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

        // Enable awkernel_lib::cpu::sleep_cpu() and awkernel_lib::cpu::wakeup_cpu().
        unsafe { awkernel_lib::cpu::init_sleep() };

        loop {
            // handle IRQs
            {
                let _irq_enable = awkernel_lib::interrupt::InterruptEnable::new();
            }

            let dur = wake_task(); // Wake executable tasks periodically.
            awkernel_lib::net::poll(); // Poll network devices.

            #[cfg(feature = "std")]
            {
                let dur = dur.unwrap_or(core::time::Duration::from_secs(1));
                awkernel_lib::select::wait(dur);
            }

            #[cfg(feature = "perf")]
            awkernel_async_lib::task::perf::start_idle();

            #[cfg(not(feature = "std"))]
            {
                let dur = dur.unwrap_or(core::time::Duration::from_secs(1));
                let us = dur.as_micros();

                if awkernel_lib::timer::is_timer_enabled() && us > 1000 {
                    let _int_guard = awkernel_lib::interrupt::InterruptGuard::new();
                    awkernel_lib::timer::reset(dur); // start timer
                    awkernel_lib::cpu::sleep_cpu();
                    awkernel_lib::timer::disable();
                } else {
                    let _irq_enable = awkernel_lib::interrupt::InterruptEnable::new();
                    awkernel_lib::delay::wait_microsec(10);
                }
            }

            #[cfg(feature = "perf")]
            awkernel_async_lib::task::perf::start_kernel();

            // Wake up other CPUs if there are any tasks to run.
            awkernel_async_lib::task::wake_workers();
        }
    }

    // Non-primary CPUs.
    while !PRIMARY_READY.load(Ordering::SeqCst) {
        awkernel_lib::delay::wait_microsec(10);
    }

    #[cfg(not(feature = "std"))]
    {
        awkernel_lib::interrupt::enable_irq(config::PREEMPT_IRQ);
        awkernel_lib::interrupt::enable_irq(config::WAKEUP_IRQ);

        if let Some(irq) = awkernel_lib::timer::irq_id() {
            awkernel_lib::interrupt::enable_irq(irq);
        }
    }

    NUM_READY_WORKER.fetch_add(1, Ordering::Relaxed);

    awkernel_lib::cpu::wait_init_sleep();

    unsafe { task::run() }; // Execute tasks.
}

#[cfg(feature = "std")]
fn make_stdin_nonblocking() -> std::io::Result<()> {
    use std::os::fd::AsRawFd;

    let stdin = std::io::stdin();
    let fd = stdin.as_raw_fd();

    awkernel_lib::file_control::set_nonblocking(fd)
}

#[cfg(not(feature = "std"))]
fn init_interrupt() {
    awkernel_lib::interrupt::set_preempt_irq(
        config::PREEMPT_IRQ,
        awkernel_async_lib::task::preemption,
        awkernel_async_lib::task::voluntary_preemption,
    );

    // IRQ for wakeup CPUs.
    awkernel_lib::interrupt::set_wakeup_irq(config::WAKEUP_IRQ);
    awkernel_lib::interrupt::enable_irq(config::WAKEUP_IRQ);
}
