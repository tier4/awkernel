//! # Awkernel
//!
//! Awkernel is a safe and realtime operating system.
//! It can execute async/await applications in kernel space safely.

#![cfg_attr(feature = "x86", feature(abi_x86_interrupt))]
#![no_main]
#![allow(unused_features)]
#![feature(allocator_api)]
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
#[cfg(feature = "period-index-propagation")]
const PERF_PRINT_INTERVAL_SECS: u64 = 30;

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
            SchedulerType::PrioritizedFIFO(31),
        );

        // Auto-trace for real hardware (no shell input available).
        #[cfg(feature = "perf")]
        spawn_auto_trace();

        // Auto-reboot for real hardware (see config::AUTO_REBOOT_* doc).
        #[cfg(all(target_arch = "x86_64", target_os = "none"))]
        spawn_auto_reboot();

        PRIMARY_READY.store(true, Ordering::SeqCst);

        // Wait until all other CPUs have incremented NUM_CPU
        while NUM_READY_WORKER.load(Ordering::SeqCst) < (kernel_info.num_cpu - 1) as u16 {
            awkernel_lib::delay::wait_microsec(10);
        }

        // Enable awkernel_lib::cpu::sleep_cpu() and awkernel_lib::cpu::wakeup_cpu().
        unsafe { awkernel_lib::cpu::init_sleep() };

        #[cfg(feature = "period-index-propagation")]
        let mut last_print = awkernel_lib::time::Instant::now();

        loop {
            #[cfg(feature = "period-index-propagation")]
            if last_print.elapsed().as_secs() >= PERF_PRINT_INTERVAL_SECS {
                // awkernel_async_lib::task::perf::print_timestamp_table();

                last_print = awkernel_lib::time::Instant::now();
            }
            // handle IRQs
            {
                let _irq_enable = awkernel_lib::interrupt::InterruptEnable::new();
            }

            let dur = wake_task(); // Wake executable tasks periodically.

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
                    awkernel_lib::cpu::sleep_cpu(Some(dur));
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

/// Spawn a task that records a task execution trace automatically after boot
/// Set by `spawn_auto_trace` right after `trace::dump_to_console()`
/// returns, so `spawn_auto_reboot` can reboot as soon as the dump is
/// actually done instead of guessing at a fixed wall-clock delay. Defined
/// unconditionally (not under `#[cfg(feature = "perf")]`) because
/// `spawn_auto_reboot` reads it regardless of whether that feature -- and
/// thus `spawn_auto_trace` itself -- is compiled in at all; if it never
/// gets set (auto-trace disabled, `perf` off, or the trace task panics),
/// `spawn_auto_reboot`'s own `AUTO_REBOOT_SECS` cap is what keeps the
/// machine from waiting forever.
static AUTO_TRACE_DONE: AtomicBool = AtomicBool::new(false);

/// Records a task execution trace automatically after boot (see
/// `config::AUTO_TRACE_*`), and dumps it to the serial console.
///
/// This replaces the shell commands on real hardware, where the serial
/// console is output-only (viewed with minicom on the host).
#[cfg(feature = "perf")]
fn spawn_auto_trace() {
    use awkernel_async_lib::task::trace;
    use core::time::Duration;

    if !config::AUTO_TRACE_ENABLED {
        return;
    }

    task::spawn(
        "[Awkernel] auto trace".into(),
        async {
            awkernel_async_lib::sleep(Duration::from_secs(config::AUTO_TRACE_START_DELAY_SECS))
                .await;

            log::info!(
                "auto trace: recording for {} seconds.",
                config::AUTO_TRACE_DURATION_SECS
            );
            trace::start();

            awkernel_async_lib::sleep(Duration::from_secs(config::AUTO_TRACE_DURATION_SECS)).await;

            trace::stop();
            log::info!("auto trace: recording finished; dumping.");
            trace::dump_to_console();
            AUTO_TRACE_DONE.store(true, Ordering::SeqCst);

            Ok(())
        },
        SchedulerType::PrioritizedFIFO(31),
    );
}

/// Reboots the machine once the auto-trace dump is confirmed done (see
/// `AUTO_TRACE_DONE`), or after `AUTO_REBOOT_SECS` regardless as a safety
/// net (auto-trace disabled/not compiled in, or its task never finishes)
/// -- see `config::AUTO_REBOOT_*`'s own doc for why a reboot is needed at
/// all here.
#[cfg(all(target_arch = "x86_64", target_os = "none"))]
fn spawn_auto_reboot() {
    use core::time::Duration;

    if !config::AUTO_REBOOT_ENABLED {
        return;
    }

    const POLL_INTERVAL_SECS: u64 = 2;

    task::spawn(
        "[Awkernel] auto reboot".into(),
        async {
            let max_polls = config::AUTO_REBOOT_SECS / POLL_INTERVAL_SECS;
            let mut polls = 0;
            while !AUTO_TRACE_DONE.load(Ordering::SeqCst) && polls < max_polls {
                awkernel_async_lib::sleep(Duration::from_secs(POLL_INTERVAL_SECS)).await;
                polls += 1;
            }

            if AUTO_TRACE_DONE.load(Ordering::SeqCst) {
                log::info!("auto reboot: trace dump confirmed done, rebooting now.");
            } else {
                log::warn!(
                    "auto reboot: trace dump never signalled done within {}s, rebooting anyway.",
                    config::AUTO_REBOOT_SECS
                );
            }
            awkernel_lib::arch::x86_64::power::reboot();
        },
        SchedulerType::PrioritizedFIFO(31),
    );
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
