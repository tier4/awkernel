#![no_std]

use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::num_cpu, delay::wait_millisec};

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
                    awkernel_async_lib::r#yield().await;
                }
            },
            SchedulerType::GEDF(1000, 60),
        )
        .await;
    // }
}
