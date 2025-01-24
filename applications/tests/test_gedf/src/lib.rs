#![no_std]

extern crate alloc;
use alloc::string::String;
use alloc::string::ToString;

use awkernel_async_lib::sleep;
use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::cpu_id, delay::wait_microsec};
use core::time::Duration;

pub async fn run() {
    wait_microsec(2000000);

    // Generate tasks with pseudo-periods.
    // Assumption that periodic reactors are running.
    // heavy_1 is preempted by light_1.
    log::info!("spawn heavy_1: {:?}", awkernel_lib::delay::uptime());
    spawn_periodic_loop("heavy_1".to_string(), 9600000, 10000000, 9900000).await; // Task id = 8
    log::info!("spawn task_1: {:?}", awkernel_lib::delay::uptime());
    spawn_periodic_loop("task_1".to_string(), 9800000, 10000000, 9800000).await; // Task id = 9
    log::info!("spawn light_1: {:?}", awkernel_lib::delay::uptime());
    spawn_periodic_loop("light_1".to_string(), 900000, 1000000, 990000).await; // Task id = 10

    wait_microsec(100000000);
}

/// Spawn a pseudo-periodic task.
async fn spawn_periodic_loop(
    task_name: String,
    exe_time: u64,
    period: u64,
    relative_deadline: u64,
) {
    let task_name_clone = task_name.clone();
    spawn(
        task_name.into(),
        async move {
            loop {
                let start_time = awkernel_lib::time::Time::now();
                wait_microsec(exe_time);
                let elapsed_time = start_time.elapsed().as_micros() as u64;
                log::debug!(
                    "task_name: {}, cpu_id: {}, start_time: {}, elapsed_time: {}",
                    task_name_clone,
                    cpu_id(),
                    start_time.uptime().as_micros() as u64,
                    elapsed_time
                );
                sleep(Duration::from_micros(period - exe_time)).await;
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::GEDF(relative_deadline),
    )
    .await;
}
