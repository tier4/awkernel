#![no_std]

use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{
    cpu::num_cpu,
    delay::{wait_microsec, wait_millisec},
};

extern crate alloc;

/// This test confirms that RR scheduler does not cause a starvation.
/// There are more tasks than num_cpu(), but all tasks will be run infinite times.
pub async fn run() {
    wait_millisec(1000);

    for i in 0..2 {
        let name = alloc::format!("long task {i}");

        spawn(
            name.into(),
            async move {
                loop {
                    // disable interrupt.
                    let _int_guard = awkernel_lib::interrupt::InterruptGuard::new();

                    log::debug!("long task {i}: cpu_id = {}", awkernel_lib::cpu::cpu_id());

                    wait_millisec(1000);
                }
            },
            SchedulerType::PrioritizedRR(0),
        )
        .await;
    }

    for i in 0..num_cpu() {
        let name = alloc::format!("short task {i}");

        spawn(
            name.into(),
            async move {
                loop {
                    wait_microsec(200);
                    awkernel_async_lib::r#yield().await;
                }
            },
            SchedulerType::PrioritizedRR(0),
        )
        .await;
    }
}
