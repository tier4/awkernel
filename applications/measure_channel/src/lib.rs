#![no_std]

extern crate alloc;

use alloc::{borrow::Cow, format, vec};
use awkernel_async_lib::{
    channel::bounded,
    pubsub::{self, create_publisher, create_subscriber},
    scheduler::SchedulerType,
    sleep, spawn, spawn_reactor, uptime_nano,
};
use core::{
    ptr::write_volatile,
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

pub async fn run() {
    for i in 0..10 {
        let (tx1, rx1) = bounded::new::<()>(bounded::Attribute::default());
        let (tx2, rx2) = bounded::new::<()>(bounded::Attribute::default());

        spawn(
            format!("{i}-server").into(),
            async move {
                loop {
                    rx1.recv().await.unwrap();
                    tx2.send(()).await.unwrap();
                }
            },
            SchedulerType::RR,
        )
        .await;

        spawn(
            format!("{i}-client").into(),
            async move {
                loop {
                    let start = uptime_nano();
                    tx1.send(()).await.unwrap();
                    rx2.recv().await.unwrap();
                    let end = uptime_nano();

                    let elapsed = end - start;

                    log::debug!("{elapsed} [ns]");
                }
            },
            SchedulerType::RR,
        )
        .await;
    }
}
