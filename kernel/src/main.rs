#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(start)]
#![feature(abi_x86_interrupt)]
#![no_std]
#![no_main]
#![allow(dead_code)]

extern crate alloc;
extern crate unwinding;

use crate::{delay::pause, scheduler::wake_task};
use alloc::boxed::Box;
use async_lib::pubsub::{create_publisher, create_subscriber, Attribute, Durability};
use core::{alloc::Layout, fmt::Debug, time::Duration};
use delay::Delay;
use kernel_info::KernelInfo;

mod arch;
mod async_lib;
mod config;
mod delay;
mod delta_list;
mod heap;
mod kernel_info;
mod logger;
mod mmio;
mod scheduler;
mod task;

fn main<Info: Debug>(kernel_info: KernelInfo<Info>) {
    log::info!("CPU#{} is starting.", kernel_info.cpu_id);

    if kernel_info.cpu_id == 0 {
        create_test_tasks();

        loop {
            wake_task();
            pause();
        }
    } else {
        task::run(kernel_info.cpu_id);
    }
}

fn create_test_tasks() {
    let publisher =
        create_publisher::<u64>("my_topic".into(), Attribute::new(10, Durability::Volatile))
            .unwrap();

    let subscriber1 =
        create_subscriber::<u64>("my_topic".into(), Attribute::new(10, Durability::Volatile))
            .unwrap();

    let subscriber2 =
        create_subscriber::<u64>("my_topic".into(), Attribute::new(10, Durability::Volatile))
            .unwrap();

    task::spawn(
        async move {
            let mut i = 0;
            loop {
                log::debug!("publisher: send {i}");
                publisher.send(i).await;
                i += 1;
                async_lib::sleep(Duration::from_secs(1)).await;
            }
        },
        scheduler::SchedulerType::RoundRobin,
    );

    task::spawn(
        async move {
            loop {
                let data = subscriber1.recv().await;
                log::debug!("subscriber 1: recv {data}");
            }
        },
        scheduler::SchedulerType::RoundRobin,
    );

    task::spawn(
        async move {
            loop {
                let data = subscriber2.recv().await;
                log::debug!("subscriber 2: recv {data}");
            }
        },
        scheduler::SchedulerType::RoundRobin,
    );

    task::spawn(
        async move {
            loop {
                log::debug!("--- Hello, T4OS! ---");

                // Test of timeout.
                async_lib::timeout(Duration::from_secs(3), async {
                    async_lib::never().await;
                })
                .await;

                // Test of yield.
                async_lib::r#yield().await;
            }
        },
        scheduler::SchedulerType::RoundRobin,
    );
}

#[alloc_error_handler]
fn on_oom(_layout: Layout) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    delay::ArchDelay::wait_forever();
}

#[cfg(any(feature = "x86", feature = "aarch64"))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    delay::ArchDelay::wait_forever();
}
