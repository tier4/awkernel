#![no_std]
use alloc::{borrow::Cow, sync::Arc};
use core::{
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};
use t4os_async_lib::{
    pubsub::{create_publisher, create_subscriber, Attribute},
    scheduler::SchedulerType,
    spawn, uptime,
};

extern crate alloc;

pub async fn main() -> Result<(), Cow<'static, str>> {
    let publisher1 =
        create_publisher::<u64>("1->2".into(), Attribute::new(1, true, false)).unwrap();
    let publisher2 =
        create_publisher::<u64>("2->1".into(), Attribute::new(1, true, false)).unwrap();

    let subscriber1 =
        create_subscriber::<u64>("1->2".into(), Attribute::new(1, true, false)).unwrap();
    let subscriber2 =
        create_subscriber::<u64>("2->1".into(), Attribute::new(1, true, false)).unwrap();

    let count1 = Arc::new(AtomicU64::new(0));
    let count2 = count1.clone();

    spawn(
        async move {
            let mut i = 0;
            loop {
                log::debug!("publish {i}");

                let start = uptime();

                publisher1.send(i).await;
                let _ = subscriber2.recv().await;

                let end = uptime();
                log::debug!("RTT: {} [us]", end - start);

                i += 1;
                t4os_async_lib::sleep(Duration::from_secs(1)).await;
            }
        },
        SchedulerType::RoundRobin,
    )
    .await;

    spawn(
        async move {
            loop {
                let data = subscriber1.recv().await;
                publisher2.send(data).await;

                log::debug!("received {data}");

                count1.fetch_add(1, Ordering::Relaxed);
            }
        },
        SchedulerType::RoundRobin,
    )
    .await;

    spawn(
        async move {
            let mut prev = 0;
            loop {
                // Test of timeout.
                t4os_async_lib::timeout(Duration::from_secs(1), async {
                    t4os_async_lib::forever().await;
                })
                .await;

                let n = count2.load(Ordering::Relaxed);
                let ops = n - prev;
                prev = n;

                log::debug!("{ops} [ops/s]");
            }
        },
        SchedulerType::RoundRobin,
    )
    .await;

    Ok(())
}
