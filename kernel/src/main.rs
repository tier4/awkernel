#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(start)]
#![feature(abi_x86_interrupt)]
#![no_std]
#![no_main]
#![allow(dead_code)]

extern crate alloc;
extern crate unwinding;

use crate::{async_lib::sleep, delay::pause, scheduler::wake_task};
use alloc::boxed::Box;
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
    task::spawn(
        async move {
            loop {
                log::debug!("*** T4 ***");
                sleep::sleep(Duration::from_secs(1)).await;
            }
        },
        scheduler::SchedulerType::RoundRobin,
    );

    task::spawn(
        async move {
            loop {
                log::debug!("--- OS ---");
                sleep::sleep(Duration::from_secs(3)).await;
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
