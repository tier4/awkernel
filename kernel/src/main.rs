//! # T4 Operating System
//!
//! T4 Operating System (T4OS) is a safe and realtime operating system
//! supporting isolated zero-copy communications written in Rust.

#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(start)]
#![feature(abi_x86_interrupt)]
#![no_std]
#![no_main]

extern crate alloc;

use alloc::{boxed::Box, sync::Arc};
use core::{
    alloc::Layout,
    fmt::Debug,
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};
use kernel_info::KernelInfo;
use t4os_async_lib::{
    pubsub::{create_publisher, create_subscriber, Attribute},
    scheduler::{wake_task, SchedulerType},
    task,
};
use t4os_lib::delay::{pause, uptime, wait_forever};

mod arch;
mod config;
mod heap;
mod kernel_info;

/// `main` function is called from each CPU.
/// `kernel_info.cpu_id` represents the CPU identifier.
/// The primary CPU's identifier is 0.
///
/// `Info` of `KernelInfo<Info>` represents architecture specific information.
fn main<Info: Debug>(kernel_info: KernelInfo<Info>) {
    log::info!("CPU#{} is starting.", kernel_info.cpu_id);

    if kernel_info.cpu_id == 0 {
        // Primary CPU.

        create_test_tasks(); // Create tasks for test. To be removed.

        loop {
            wake_task(); // Wake executable tasks periodically.
            pause();
        }
    } else {
        // Non-primary CPUs.
        task::run(kernel_info.cpu_id); // Execute tasks.
    }
}

fn create_test_tasks() {
    let publisher1 = create_publisher::<u64>("1->2".into(), Attribute::new(1)).unwrap();
    let publisher2 = create_publisher::<u64>("2->1".into(), Attribute::new(1)).unwrap();

    let subscriber1 = create_subscriber::<u64>("1->2".into(), Attribute::new(1)).unwrap();
    let subscriber2 = create_subscriber::<u64>("2->1".into(), Attribute::new(1)).unwrap();

    let count1 = Arc::new(AtomicU64::new(0));
    let count2 = count1.clone();

    task::spawn(
        async move {
            let mut i = 0;
            loop {
                log::debug!("publish {i}");

                let start = uptime();

                publisher1.send(i).await;
                let _ = subscriber2.recv().await;

                let end = uptime();
                log::debug!("RTT: {} [us]", end - start);

                i += 1;
                t4os_async_lib::sleep(Duration::from_secs(1)).await;
            }
        },
        SchedulerType::RoundRobin,
    );

    task::spawn(
        async move {
            loop {
                let data = subscriber1.recv().await;
                publisher2.send(data).await;

                log::debug!("received {data}");

                count1.fetch_add(1, Ordering::Relaxed);
            }
        },
        SchedulerType::RoundRobin,
    );

    task::spawn(
        async move {
            let mut prev = 0;
            loop {
                // Test of timeout.
                t4os_async_lib::timeout(Duration::from_secs(1), async {
                    t4os_async_lib::forever().await;
                })
                .await;

                let n = count2.load(Ordering::Relaxed);
                let ops = n - prev;
                prev = n;

                log::debug!("{ops} [ops/s]");
            }
        },
        SchedulerType::RoundRobin,
    );
}

#[alloc_error_handler]
fn on_oom(_layout: Layout) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    wait_forever();
}

#[cfg(any(feature = "x86", feature = "aarch64"))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    wait_forever();
}
