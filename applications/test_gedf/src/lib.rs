#![no_std]

use awkernel_async_lib::task::get_current_task;
use awkernel_async_lib::{scheduler::gedf::ignition_task, scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::cpu_id, cpu::num_cpu, delay::wait_millisec};

/// This test confirms that RR scheduler does not cause a starvation.
/// There are more tasks than num_cpu(), but all tasks will be run infinite times.
pub async fn run() {
    wait_millisec(1000);

    log::debug!("test gedf num_cpu={}", num_cpu());

    // for i in 1..num_cpu() * 2 {
    spawn(
        "infinite_loop".into(),
        async move {
            loop {
                log::debug!("infinite loop task, no=1");
                wait_millisec(100);
                ignition_task(get_current_task(cpu_id()).unwrap());
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::GEDF(1000000, 60, awkernel_lib::delay::uptime()),
    )
    .await;
    // }
}
