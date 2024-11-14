#![no_std]

extern crate alloc;

use alloc::{format, sync::Arc, vec::Vec};
use awkernel_async_lib::{
    channel::bounded,
    pubsub::{self, Attribute, Publisher, Subscriber},
    scheduler::SchedulerType,
    spawn, uptime_nano,
};
use core::{sync::atomic::AtomicUsize, time::Duration};
use serde::Serialize;

const NUM_TASKS: [usize; 7] = [1000, 10, 200, 400, 600, 800, 1000];
const NUM_BYTES: [usize; 6] = [128, 2048, 8192, 8192 * 2, 8192 * 3, 8192 * 4];
const NUM_TRIAL: usize = 10000;

#[derive(Serialize)]
struct MeasureResult {
    num_task: usize,
    num_bytes: usize,
    worst: f64,
    p99: f64,
    p90: f64,
    p50: f64,
    average: f64,
}

#[derive(Clone)]
struct Barrier {
    count: Arc<AtomicUsize>,
    tx: Arc<Publisher<()>>,
    rx: Subscriber<()>,
}

impl Barrier {
    fn new(count: usize) -> Self {
        let attr = Attribute {
            queue_size: 1,
            ..Attribute::default()
        };
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
    let mut result = alloc::vec::Vec::with_capacity(NUM_TASKS.len());
    for num_task in NUM_TASKS.iter() {
        for num_bytes in NUM_BYTES.iter() {
            let ms = measure_task(*num_task, *num_bytes).await;
            result.push(ms);
        }
    }

    let json = serde_json::to_string(&result).unwrap();
    log::debug!("\r\n{}", json);
}

async fn measure_task(num_task: usize, num_bytes: usize) -> MeasureResult {
    let barrier = Barrier::new(num_task * 2);
    let mut server_join = alloc::vec::Vec::new();
    let mut client_join = alloc::vec::Vec::new();

    for i in 0..num_task {
        let (tx1, rx1) = bounded::new::<Vec<u8>>(bounded::Attribute::default());
        let (tx2, rx2) = bounded::new::<Vec<u8>>(bounded::Attribute::default());

        let mut barrier2 = barrier.clone();
        let hdl = spawn(
            format!("{i}-server").into(),
            async move {
                barrier2.wait().await;

                for _ in 0..NUM_TRIAL {
                    if let Ok(data) = rx1.recv().await {
                        awkernel_lib::delay::wait_microsec(50); // Simulate processing time.

                        if tx2.send(data).await.is_err() {
                            return;
                        }
                    } else {
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
                client_task(tx1, rx2, num_bytes).await
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
    let average = result.iter().sum::<u128>() as f64 / result.len() as f64 / 1_000_000_000.0;

    log::debug!("result:");
    log::debug!("  num_task        = {num_task}");
    log::debug!("  num_bytes       = {num_bytes}");
    log::debug!("  worst case      = {worst} [s]");
    log::debug!("  99th percentile = {p99} [s]");
    log::debug!("  90th percentile = {p90} [s]");
    log::debug!("  50th percentile = {p50} [s]");
    log::debug!("  average         = {average} [s]");

    MeasureResult {
        num_task,
        num_bytes,
        worst,
        p99,
        p90,
        p50,
        average,
    }
}

async fn client_task(
    tx1: bounded::Sender<Vec<u8>>,
    rx2: bounded::Receiver<Vec<u8>>,
    buf_size: usize,
) -> alloc::vec::Vec<u128> {
    let mut result = alloc::vec::Vec::with_capacity(NUM_TRIAL);

    let mut buf = Vec::with_capacity(buf_size);
    for i in 0..buf_size {
        buf.push(i as u8);
    }

    for _ in 0..NUM_TRIAL {
        let start = uptime_nano();
        tx1.send(buf).await.unwrap();
        buf = rx2.recv().await.unwrap();
        let end = uptime_nano();

        if start <= end {
            let elapsed = end - start;
            result.push(elapsed);
        }
    }

    awkernel_async_lib::sleep(Duration::from_secs(3)).await;

    result
}
