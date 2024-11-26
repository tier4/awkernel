#![no_std]

extern crate alloc;

use core::time::Duration;

use alloc::sync::Arc;
use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::num_cpu, delay::wait_microsec, sync::bravo_rwlock::BravoRwLock};

pub async fn run() {
    let data = Arc::new(BravoRwLock::new(false));

    for i in 0..(num_cpu() - 1) {
        let d = data.clone();

        // prepare reader tasks
        spawn(
            "reader".into(),
            async move {
                loop {
                    {
                        let guard = d.read();
                        if *guard {
                            // data must be false during the read operation
                            log::debug!("invalid, no={i}");
                        }
                    }

                    awkernel_async_lib::r#yield().await;
                }
            },
            SchedulerType::FIFO,
        )
        .await;
    }

    // prepare writer task
    spawn(
        "writer".into(),
        async move {
            loop {
                {
                    let mut guard = data.write();
                    *guard = true; // set true during the write operation
                    wait_microsec(2000);
                    *guard = false;
                }

                awkernel_async_lib::sleep(Duration::from_millis(10)).await;
            }
        },
        SchedulerType::FIFO,
    )
    .await;
}
