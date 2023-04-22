#![no_std]
use alloc::{borrow::Cow, sync::Arc};
use awkernel_async_lib::{
    pubsub::{create_publisher, create_subscriber, Attribute},
    scheduler::SchedulerType,
    spawn, uptime,
};
use core::{
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

extern crate alloc;

pub async fn main() -> Result<(), Cow<'static, str>> {
    let publisher1 = create_publisher::<u64>("1->2".into(), Attribute::default()).unwrap();
    let publisher2 = create_publisher::<u64>("2->1".into(), Attribute::default()).unwrap();

    let subscriber1 = create_subscriber::<u64>("1->2".into(), Attribute::default()).unwrap();
    let subscriber2 = create_subscriber::<u64>("2->1".into(), Attribute::default()).unwrap();

    let count1 = Arc::new(AtomicUsize::new(0));
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
                awkernel_async_lib::sleep(Duration::from_secs(1)).await;
            }
        },
        SchedulerType::RoundRobin,
    )
    .await;

    spawn(
        async move {
            loop {
                let data = subscriber1.recv().await;
                publisher2.send(data.data).await;

                log::debug!("received {}", data.data);

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
                awkernel_async_lib::timeout(Duration::from_secs(1), async {
                    awkernel_async_lib::forever().await;
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

    test_session_types().await;

    Ok(())
}

use awkernel_async_lib::{service, session_types::*};

// Define protocol.
type Server = Recv<u64, Send<bool, Eps>>;
type Client = <Server as HasDual>::Dual;

async fn srv(c: Chan<(), Server>) {
    let (c, n) = c.recv().await;
    let c = if n % 2 == 0 {
        c.send(true).await
    } else {
        c.send(false).await
    };
    c.close();
}

async fn cli(c: Chan<(), Client>) {
    let c = c.send(9).await;
    let (c, result) = c.recv().await;
    c.close();

    log::debug!("cli: result = {result}");
}

async fn test_session_types() {
    // Start a server.
    let accepter = service::create_server::<Server>("simple service".into()).unwrap();

    // Spawn a connection accepter.
    awkernel_async_lib::spawn(
        async move {
            while let Ok(chan) = accepter.accept().await {
                // Spawn a task for the connection.
                awkernel_async_lib::spawn(
                    async move {
                        srv(chan).await;
                    },
                    SchedulerType::RoundRobin,
                )
                .await;
            }
        },
        SchedulerType::RoundRobin,
    )
    .await;

    // Start a client.
    awkernel_async_lib::spawn(
        async {
            let chan = service::create_client::<Client>("simple service".into())
                .await
                .unwrap();
            cli(chan).await;
        },
        SchedulerType::RoundRobin,
    )
    .await;
}
