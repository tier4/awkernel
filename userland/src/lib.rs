#![no_std]
use alloc::{borrow::Cow, format};
use awkernel_async_lib::{
    pubsub::{create_publisher, create_subscriber, Attribute},
    scheduler::SchedulerType,
    spawn, uptime,
};
use core::{
    ptr::{read_volatile, write_volatile},
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

extern crate alloc;

const RTT_SIZE: usize = 1024 * 8;

static mut RTT: [u64; RTT_SIZE] = [0; RTT_SIZE];
static COUNT: AtomicUsize = AtomicUsize::new(0);

fn add_rtt(rtt: u64) {
    let index = COUNT.fetch_add(1, Ordering::Relaxed);
    unsafe { write_volatile(&mut RTT[index & (RTT_SIZE - 1)], rtt) };
}

pub async fn main() -> Result<(), Cow<'static, str>> {
    awkernel_shell::init();

    spawn(
        async move {
            loop {
                awkernel_async_lib::sleep(Duration::from_secs(2)).await;

                let mut total = 0;
                let mut count = 0;
                let mut worst = 0;

                for i in 0..RTT_SIZE {
                    let rtt = unsafe { read_volatile(&RTT[i]) };
                    if rtt > 0 {
                        total += rtt;
                        count += 1;
                    }

                    if rtt > worst {
                        worst = rtt;
                    }
                }

                if count > 0 {
                    let ave = total as f64 / count as f64;
                    log::debug!("RTT: ave = {ave:.2} [us], worst = {worst} [us]");
                }
            }
        },
        SchedulerType::RoundRobin,
    )
    .await;

    for i in 0..64 {
        let topic_a = format!("topic_a_{i}");
        let topic_b = format!("topic_b_{i}");

        let publisher1 =
            create_publisher::<()>(topic_a.clone().into(), Attribute::default()).unwrap();
        let subscriber1 =
            create_subscriber::<()>(topic_b.clone().into(), Attribute::default()).unwrap();

        let publisher2 = create_publisher::<()>(topic_b.into(), Attribute::default()).unwrap();
        let subscriber2 = create_subscriber::<()>(topic_a.into(), Attribute::default()).unwrap();

        spawn(
            async move {
                loop {
                    subscriber2.recv().await;
                    publisher2.send(()).await;
                }
            },
            SchedulerType::RoundRobin,
        )
        .await;

        spawn(
            async move {
                loop {
                    let start = uptime();
                    publisher1.send(()).await;
                    subscriber1.recv().await;
                    let end = uptime();

                    let elapsed = end - start;
                    add_rtt(elapsed);

                    awkernel_async_lib::sleep(Duration::from_millis(100)).await;
                }
            },
            SchedulerType::RoundRobin,
        )
        .await;
    }

    Ok(())
}
