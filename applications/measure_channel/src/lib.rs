#![no_std]

extern crate alloc;

use core::{sync::atomic::AtomicUsize, time::Duration};

use alloc::{format, sync::Arc};
use awkernel_async_lib::{
    channel::bounded,
    pubsub::{self, Attribute, Publisher, Subscriber},
    scheduler::SchedulerType,
    spawn, uptime_nano,
};

const NUM_TASK: usize = 1000;
const NUM_TRIAL: usize = 10000;

#[derive(Clone)]
struct Barrier {
    count: Arc<AtomicUsize>,
    tx: Arc<Publisher<()>>,
    rx: Subscriber<()>,
}

impl Barrier {
    fn new(count: usize) -> Self {
        let mut attr = Attribute::default();
        attr.queue_size = 1;
        let (tx, rx) = pubsub::create_pubsub(attr);

        Self {
            count: Arc::new(AtomicUsize::new(count)),
            tx: Arc::new(tx),
            rx,
        }
    }

    async fn wait(&mut self) {
        if self
            .count
            .fetch_sub(1, core::sync::atomic::Ordering::Relaxed)
            == 1
        {
            self.tx.send(()).await;
        } else {
            self.rx.recv().await;
        }
    }
}

pub async fn run() {
    let barrier = Barrier::new(NUM_TASK * 2);
    let mut server_join = alloc::vec::Vec::new();
    let mut client_join = alloc::vec::Vec::new();

    for i in 0..NUM_TASK {
        let (tx1, rx1) = bounded::new::<()>(bounded::Attribute::default());
        let (tx2, rx2) = bounded::new::<()>(bounded::Attribute::default());

        let mut barrier2 = barrier.clone();
        let hdl = spawn(
            format!("{i}-server").into(),
            async move {
                barrier2.wait().await;

                for _ in 0..NUM_TRIAL {
                    if rx1.recv().await.is_err() {
                        return;
                    }

                    awkernel_lib::delay::wait_microsec(50);

                    if tx2.send(()).await.is_err() {
                        return;
                    }
                }
            },
            SchedulerType::RR,
        )
        .await;

        server_join.push(hdl);

        let mut barrier2 = barrier.clone();
        let hdl = spawn(
            format!("{i}-client").into(),
            async move {
                barrier2.wait().await;
                client_task(tx1, rx2).await
            },
            SchedulerType::RR,
        )
        .await;

        client_join.push(hdl);
    }

    for hdl in server_join {
        let _ = hdl.join().await;
    }

    let mut result = alloc::vec::Vec::new();

    for hdl in client_join {
        if let Ok(v) = hdl.join().await {
            result.extend(v);
        }
    }

    result.sort_unstable();

    let worst = *result.last().unwrap() as f64 / 1_000_000_000.0;
    let p99 = *result.get((result.len() as f64 * 0.99) as usize).unwrap() as f64 / 1_000_000_000.0;
    let p90 = *result.get((result.len() as f64 * 0.90) as usize).unwrap() as f64 / 1_000_000_000.0;
    let p50 = *result.get((result.len() as f64 * 0.50) as usize).unwrap() as f64 / 1_000_000_000.0;

    log::debug!("worst case      = {worst} [s]");
    log::debug!("99th percentile = {p99} [s]");
    log::debug!("90th percentile = {p90} [s]");
    log::debug!("50th percentile = {p50} [s]");
}

async fn client_task(
    tx1: bounded::Sender<()>,
    rx2: bounded::Receiver<()>,
) -> alloc::vec::Vec<u128> {
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

    result
}
