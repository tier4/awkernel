#![no_std]
use alloc::{borrow::Cow, format};
use awkernel_async_lib::{
    channel::bounded,
    pubsub::{self, create_publisher, create_subscriber},
    scheduler::SchedulerType,
    sleep, spawn,
    task::perf::add_context_restore_end,
    uptime,
};
use core::{
    ptr::write_volatile,
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
                awkernel_async_lib::sleep(Duration::from_secs(10)).await;

                // let mut total = 0;
                // let mut count = 0;
                // let mut worst = 0;

                // #[allow(clippy::needless_range_loop)]
                // for i in 0..RTT_SIZE {
                //     let rtt = unsafe { read_volatile(&RTT[i]) };
                //     if rtt > 0 {
                //         total += rtt;
                //         count += 1;
                //     }

                //     if rtt > worst {
                //         worst = rtt;
                //     }
                // }

                // if count > 0 {
                //     let ave = total as f64 / count as f64;
                //     log::debug!("RTT: ave = {ave:.2} [us], worst = {worst} [us]");
                // }

                // let (save_ave, save_worst, restore_ave, restore_worst) =
                //     calc_context_switch_overhead();
                // log::debug!("Context save: ave = {save_ave:.2} [us], worst = {save_worst} [us]");
                // log::debug!(
                //     "Context restore: ave = {restore_ave:.2} [us], worst = {restore_worst} [us]"
                // );
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

    #[cfg(feature = "raspi")]
    spawn(
        "awkernel_ydlidar_driver".into(),
        awkernel_ydlidar_driver::run_ydlidar_driver(),
        SchedulerType::FIFO,
    )
    .await;

    Ok(())
}
