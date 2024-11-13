#![no_std]

use awkernel_async_lib::scheduler::gedf;
use awkernel_async_lib::task::get_current_task;
use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::cpu_id, cpu::num_cpu, delay::wait_millisec};

/// This test verifies that the GEDF scheduler adheres to the startup order and startup timing.
pub async fn run() {
    wait_millisec(1000);

    log::debug!("test gedf num_cpu={}", num_cpu());

    // for i in 1..num_cpu() * 2 {
    spawn(
        "infinite_loop".into(),
        async move {
            gedf::SCHEDULER.register_task(get_current_task(cpu_id()).unwrap());
            loop {
                log::debug!(
                    "infinite loop task, task_id={}",
                    get_current_task(cpu_id()).unwrap()
                );
                wait_millisec(100);
                gedf::SCHEDULER.increment_ignition(get_current_task(cpu_id()).unwrap());
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::GEDF(1000000, 60, awkernel_lib::delay::uptime()),
    )
    .await;
    // }
}
