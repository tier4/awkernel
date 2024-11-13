#![no_std]

extern crate alloc;

use core::time::Duration;

use alloc::format;
use awkernel_async_lib::{channel::bounded, scheduler::SchedulerType, spawn, uptime_nano};

pub async fn run() {
    for i in 0..100 {
        let (tx1, rx1) = bounded::new::<()>(bounded::Attribute::default());
        let (tx2, rx2) = bounded::new::<()>(bounded::Attribute::default());

        spawn(
            format!("{i}-server").into(),
            async move {
                loop {
                    if rx1.recv().await.is_err() {
                        return;
                    }

                    if tx2.send(()).await.is_err() {
                        return;
                    }
                }
            },
            SchedulerType::RR,
        )
        .await;

        spawn(
            format!("{i}-client").into(),
            async move {
                client_task(tx1, rx2).await;
            },
            SchedulerType::RR,
        )
        .await;
    }
}

const NUM_TRIAL: usize = 10000;

async fn client_task(tx1: bounded::Sender<()>, rx2: bounded::Receiver<()>) {
    let mut result = alloc::vec::Vec::with_capacity(NUM_TRIAL);

    for _ in 0..NUM_TRIAL {
        let start = uptime_nano();
        tx1.send(()).await.unwrap();
        rx2.recv().await.unwrap();
        let end = uptime_nano();

        let elapsed = end - start;

        result.push(elapsed);
    }

    awkernel_async_lib::sleep(Duration::from_secs(3)).await;

    result.sort();

    let p99 = result[NUM_TRIAL / 100 * 99]; // 99th percentile

    log::debug!("99th percentile =  {p99} [ns]");
}
