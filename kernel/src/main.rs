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
            SchedulerType::PrioritizedFIFO(31),
        );

        PRIMARY_READY.store(true, Ordering::SeqCst);

        // Wait until all other CPUs have incremented NUM_CPU
        while NUM_READY_WORKER.load(Ordering::SeqCst) < (kernel_info.num_cpu - 1) as u16 {
            awkernel_lib::delay::wait_microsec(10);
        }

        // Enable awkernel_lib::cpu::sleep_cpu() and awkernel_lib::cpu::wakeup_cpu().
        unsafe { awkernel_lib::cpu::init_sleep() };

        let mut last_print = awkernel_lib::time::Time::now();

        loop {
            if last_print.elapsed().as_secs() >= 30 {
                #[cfg(feature = "perf")]
                awkernel_async_lib::task::perf::print_timestamp_table();
                // awkernel_async_lib::task::perf::print_node_table();
                // awkernel_async_lib::task::perf::print_pubsub_table();
                // print_perf_to_console();
                // print_task_to_console();

                last_print = awkernel_lib::time::Time::now();
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

fn print_task_to_console() {
    use awkernel_lib::console;
    use awkernel_lib::sync::mutex::MCSNode;

    console::print("\r\n=== Task Report ===\r\n");

    let msg = alloc::format!("Uptime: {}\r\n", awkernel_async_lib::uptime());
    console::print(&msg);

    print_tasks();

    console::print("\r\n");

    let msg = alloc::format!(
        "Total preemption: {}\r\n",
        awkernel_async_lib::task::get_num_preemption(),
    );
    console::print(&msg);

    console::print("Running Tasks:\r\n");
    for task in awkernel_async_lib::task::get_tasks_running().iter() {
        let msg = if task.task_id != 0 {
            alloc::format!("  cpu: {:>3}, task: {:>5}\r\n", task.cpu_id, task.task_id)
        } else {
            alloc::format!("  cpu: {:>3}, task:\r\n", task.cpu_id)
        };
        console::print(&msg);
    }

    console::print("=== End of Task Report ===\r\n\r\n");
}

fn print_tasks() {
    use awkernel_lib::console;
    use awkernel_lib::sync::mutex::MCSNode;

    let tasks = task::get_tasks();

    console::print("Tasks:\r\n");

    let msg = alloc::format!(
        "{:>5}  {:<10} {:>14} {:>14} name\r\n",
        "ID", "State", "#Preemption", "Last Executed"
    );
    console::print(&msg);

    for t in tasks {
        let mut node = MCSNode::new();
        let info = t.info.lock(&mut node);

        let state = alloc::format!("{:?}", info.get_state());

        let msg = alloc::format!(
            "{:>5}{} {:<10} {:>14} {:>14} {}\r\n",
            t.id,
            if info.panicked() { "*" } else { " " },
            state,
            info.get_num_preemption(),
            info.get_last_executed().uptime().as_micros(),
            t.name,
        );

        console::print(&msg);
    }
}

#[cfg(feature = "perf")]
fn print_perf_to_console() {
    use awkernel_lib::console;
    use awkernel_async_lib::task::perf;

    console::print("\r\n=== Performance Report ===\r\n");
    console::print("Perform non-primary CPU [tsc]:\r\n");
    console::print(" cpu | Type           |   kernel_time  |    task_time   |    idle_time   | interrupt_time | context_switch |    perf_time   \r\n");
    console::print("=====|================|================|================|================|================|================|================\r\n");

    let mut total_kernel = 0u64;
    let mut total_task = 0u64;
    let mut total_idle = 0u64;
    let mut total_interrupt = 0u64;
    let mut total_context_switch = 0u64;
    let mut total_perf = 0u64;

    for cpu_id in 0..awkernel_lib::cpu::num_cpu() {
        let kernel_time = perf::get_kernel_time(cpu_id);
        let task_time = perf::get_task_time(cpu_id);
        let idle_time = perf::get_idle_time(cpu_id);
        let interrupt_time = perf::get_interrupt_time(cpu_id);
        let contxt_switch_time = perf::get_context_switch_time(cpu_id);
        let perf_time = perf::get_perf_time(cpu_id);

        // Exclude cpu_id=0 from overall statistics
        if cpu_id != 0 {
            total_kernel += kernel_time;
            total_task += task_time;
            total_idle += idle_time;
            total_interrupt += interrupt_time;
            total_context_switch += contxt_switch_time;
            total_perf += perf_time;
        }

        let msg = alloc::format!(
            "{cpu_id:>4} | Total          |{kernel_time:>15} |{task_time:>15} |{idle_time:>15} |{interrupt_time:>15} |{contxt_switch_time:>15} |{perf_time:>15}\r\n"
        );
        console::print(&msg);

        let ave_kernel_time = perf::get_ave_kernel_time(cpu_id).unwrap_or(0.0);
        let ave_task_time = perf::get_ave_task_time(cpu_id).unwrap_or(0.0);
        let ave_idle_time = perf::get_ave_idle_time(cpu_id).unwrap_or(0.0);
        let ave_interrupt_time = perf::get_ave_interrupt_time(cpu_id).unwrap_or(0.0);
        let ave_contxt_switch_time = perf::get_ave_context_switch_time(cpu_id).unwrap_or(0.0);
        let ave_perf_time = perf::get_ave_perf_time(cpu_id).unwrap_or(0.0);

        let msg_ave = alloc::format!(
            "     | Avg            | {ave_kernel_time:>14.2} | {ave_task_time:>14.2} |{ave_idle_time:>15.2} |{ave_interrupt_time:>15.2} |{ave_contxt_switch_time:>15.2} |{ave_perf_time:>15.2}\r\n",
        );
        console::print(&msg_ave);

        let worst_kernel_time = perf::get_kernel_wcet(cpu_id);
        let worst_task_time = perf::get_task_wcet(cpu_id);
        let worst_idle_time = perf::get_idle_wcet(cpu_id);
        let worst_interrupt_time = perf::get_interrupt_wcet(cpu_id);
        let worst_contxt_switch_time = perf::get_context_switch_wcet(cpu_id);
        let worst_perf_time = perf::get_perf_wcet(cpu_id);

        let msg_worst = alloc::format!(
            "     | Worst          | {worst_kernel_time:>14} | {worst_task_time:>14} |{worst_idle_time:>15} |{worst_interrupt_time:>15} |{worst_contxt_switch_time:>15} |{worst_perf_time:>15}\r\n",
        );
        console::print(&msg_worst);

        // Calculate and display per-core CPU usage
        let cpu_total = kernel_time + task_time + idle_time + interrupt_time + contxt_switch_time + perf_time;
        if cpu_total > 0 {
            let cpu_usage = (cpu_total - idle_time) as f64 / cpu_total as f64 * 100.0;
            let msg_usage = alloc::format!(
                "     | CPU Usage      | {cpu_usage:>13.2}%\r\n"
            );
            console::print(&msg_usage);
        }

        if cpu_id < awkernel_lib::cpu::num_cpu() - 1 {
            console::print("-----|----------------|----------------|----------------|----------------|----------------|----------------|----------------\r\n");
        }
    }

    // Calculate and display overall CPU usage (excluding cpu_id=0)
    console::print("=====|================|================|================|================|================|================|================\r\n");
    let grand_total = total_kernel + total_task + total_idle + total_interrupt + total_context_switch + total_perf;
    if grand_total > 0 {
        let overall_cpu_usage = (grand_total - total_idle) as f64 / grand_total as f64 * 100.0;
        let num_worker_cores = awkernel_lib::cpu::num_cpu() - 1;
        let msg_overall = alloc::format!(
            "Overall CPU Usage: {overall_cpu_usage:>6.2}% (across {} worker cores, excluding CPU0)\r\n",
            num_worker_cores
        );
        console::print(&msg_overall);
    }

    console::print("=== End of Performance Report ===\r\n\r\n");
}
