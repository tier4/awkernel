#![no_std]

extern crate alloc;

use core::time::Duration;

use alloc::sync::Arc;
use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::num_cpu, delay::wait_microsec, sync::bravo_rwlock::BravoRwLock};

/// This test confirms that RR scheduler does not cause a starvation.
/// There are more tasks than num_cpu(), but all tasks will be run infinite times.
pub async fn run() {
    let data = Arc::new(BravoRwLock::new(false));

    for i in 0..(num_cpu() - 1) {
        let d = data.clone();
        spawn(
            "reader".into(),
            async move {
                loop {
                    // let guard = d.read();
                    // if *guard {
                    //     log::debug!("invalid, no={i}");
                    // }

                    awkernel_async_lib::r#yield().await;
                }
            },
            SchedulerType::FIFO,
        )
        .await;
    }

    spawn(
        "writer".into(),
        async move {
            loop {
                {
                    // let mut guard = data.write();
                    // *guard = true;
                    wait_microsec(50);
                    // *guard = false;
                }

                awkernel_async_lib::sleep(Duration::from_millis(10)).await;
            }
        },
        SchedulerType::FIFO,
    )
    .await;
}
