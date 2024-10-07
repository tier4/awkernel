#![no_std]

extern crate alloc;

use alloc::{borrow::Cow, format, string::String, vec};
use awkernel_async_lib::{
    channel::bounded,
    pubsub::{self, create_publisher, create_subscriber},
    scheduler::SchedulerType,
    sleep, spawn, spawn_reactor,
    task::perf::add_context_restore_end,
    uptime,
};
use core::{
    ptr::write_volatile,
    str::FromStr,
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

const RTT_SIZE: usize = 1024 * 8;

static mut RTT: [u64; RTT_SIZE] = [0; RTT_SIZE];
static COUNT: AtomicUsize = AtomicUsize::new(0);

fn add_rtt(rtt: u64) {
    let index = COUNT.fetch_add(1, Ordering::Relaxed);
    unsafe { write_volatile(&mut RTT[index & (RTT_SIZE - 1)], rtt) };
}

pub async fn run() {
    spawn(
        "panic".into(),
        async move {
            panic!("panic test");
        },
        SchedulerType::FIFO,
    )
    .await;

    spawn(
        "timer".into(),
        async move {
            loop {
                log::debug!("timer is invoked.");
                awkernel_async_lib::sleep(Duration::from_secs(10)).await;
            }
        },
        SchedulerType::FIFO,
    )
    .await;

    for i in 0..8 {
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
            SchedulerType::FIFO,
        )
        .await;

        spawn(
            format!("{i}-client").into(),
            async move {
                loop {
                    let start = uptime();
                    tx1.send(()).await.unwrap();
                    rx2.recv().await.unwrap();
                    let end = uptime();

                    let elapsed = end - start;
                    add_rtt(elapsed);

                    for _ in 0..1_000_000 {
                        unsafe { core::arch::asm!("nop") };
                    }
                }
            },
            SchedulerType::FIFO,
        )
        .await;
    }

    for i in 0..4 {
        let name = format!("pubsub[{i}]");
        let subscriber =
            create_subscriber::<()>(name.clone().into(), pubsub::Attribute::default()).unwrap();
        let publisher = create_publisher::<()>(name.into(), pubsub::Attribute::default()).unwrap();

        spawn(
            format!("{i}-subscriber").into(),
            async move {
                loop {
                    subscriber.recv().await;
                    // Only the subscriber's cooperative context switch overhead is measured.
                    add_context_restore_end(awkernel_async_lib::cpu_id(), uptime());
                }
            },
            SchedulerType::FIFO,
        )
        .await;

        spawn(
            format!("{i}-publisher").into(),
            async move {
                loop {
                    sleep(Duration::from_secs(1)).await;
                    publisher.send(()).await;
                }
            },
            SchedulerType::FIFO,
        )
        .await;
    }

    spawn(
        "hoge".into(),
        async move {
            let publisher =
                create_publisher::<i32>("topic1".into(), pubsub::Attribute::default()).unwrap();
            loop {
                sleep(Duration::from_secs(1)).await;
                publisher.send(1 as i32);
            }
        },
        SchedulerType::FIFO,
    )
    .await;

    spawn(
        "fuga".into(),
        async move {
            let publisher =
                create_publisher::<String>("topic2".into(), pubsub::Attribute::default()).unwrap();
            loop {
                sleep(Duration::from_secs(1)).await;
                publisher.send(String::from_str("1").unwrap());
            }
        },
        SchedulerType::FIFO,
    )
    .await;

    let f = |(a, b): (i32, String)| -> (f64, bool) {
        log::debug!("hello from reactor");
        (a as f64, b.is_empty())
    };

    let ret = spawn_reactor::<_, (i32, String), _>(
        "my_reactor".into(),
        f,
        vec![Cow::from("topic1"), Cow::from("topic2")],
        vec![Cow::from("result1"), Cow::from("result2")],
        SchedulerType::FIFO,
    )
    .await;
}
