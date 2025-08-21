#![no_std]

extern crate alloc;

use alloc::{format, sync::Arc, vec::Vec};
use awkernel_async_lib::{
    channel::bounded,
    pubsub::{self, Attribute, Publisher, Subscriber},
    scheduler::SchedulerType,
    spawn, uptime_nano,
};
use core::sync::atomic::{AtomicBool, AtomicUsize};
use serde::Serialize;

const NUM_HEAVY: usize = 60;
const NUM_TRIAL: usize = 10000;
const NUM_TASK: usize = 1000;

#[derive(Serialize)]
struct MeasureResult {
    num_task: usize,
    num_heavy: usize,
    is_heavy: bool,
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
    let mut result = alloc::vec::Vec::with_capacity(NUM_HEAVY >> 1);
    for num_heavy in (2..=NUM_HEAVY).step_by(2) {
        let (ms0, ms1) = measure_task(num_heavy).await;
        result.push(ms0);
        result.push(ms1);
    }

    let json = serde_json::to_string(&result).unwrap();
    log::debug!("\r\n{}", json);
}

async fn measure_task(num_heavy: usize) -> (MeasureResult, MeasureResult) {
    let barrier = Barrier::new(NUM_TASK * 2);
    let barrier_end = Barrier::new(NUM_TASK - num_heavy);
    let is_finished = Arc::new(AtomicBool::new(false));

    let mut server_join = alloc::vec::Vec::new();
    let mut client_join = alloc::vec::Vec::new();

    for i in 0..NUM_TASK {
        let (tx1, rx1) = bounded::new::<bool>(bounded::Attribute::default());
        let (tx2, rx2) = bounded::new::<bool>(bounded::Attribute::default());

        let is_heavy = i < num_heavy;

        let mut barrier2 = barrier.clone();
        let hdl = spawn(
            format!("{i}-server").into(),
            async move {
                barrier2.wait().await;

                for _ in 0..NUM_TRIAL {
                    if let Ok(data) = rx1.recv().await {
                        // Simulate processing time.
                        if is_heavy {
                            awkernel_lib::delay::wait_millisec(50);
                        } else {
                            awkernel_lib::delay::wait_microsec(50);
                        }

                        if tx2.send(data).await.is_err() {
                            return;
                        }

                        if data {
                            break;
                        }
                    } else {
                        return;
                    }
                }
            },
            SchedulerType::PrioritizedRR(0),
        )
        .await;

        server_join.push(hdl);

        let mut barrier2 = barrier.clone();
        let barrier_end = barrier_end.clone();
        let is_finished = is_finished.clone();
        let hdl = spawn(
            format!("{i}-client").into(),
            async move {
                barrier2.wait().await;
                client_task(tx1, rx2, is_heavy, is_finished, barrier_end).await
            },
            SchedulerType::PrioritizedRR(0),
        )
        .await;

        client_join.push(hdl);
    }

    for hdl in server_join {
        let _ = hdl.join().await;
    }

    let mut result_light = alloc::vec::Vec::new();
    let mut result_heavy = alloc::vec::Vec::new();

    for hdl in client_join {
        if let Ok((is_heavy, v)) = hdl.join().await {
            if is_heavy {
                result_heavy.extend(v);
            } else {
                result_light.extend(v);
            }
        }
    }

    result_light.sort_unstable();
    result_heavy.sort_unstable();

    (
        get_result(&result_heavy, num_heavy, true),
        get_result(&result_light, num_heavy, false),
    )
}

fn get_result(rtt: &Vec<u128>, num_heavy: usize, is_heavy: bool) -> MeasureResult {
    let worst = *rtt.last().unwrap() as f64 / 1_000_000_000.0;
    let p99 = *rtt.get((rtt.len() as f64 * 0.99) as usize).unwrap() as f64 / 1_000_000_000.0;
    let p90 = *rtt.get((rtt.len() as f64 * 0.90) as usize).unwrap() as f64 / 1_000_000_000.0;
    let p50 = *rtt.get((rtt.len() as f64 * 0.50) as usize).unwrap() as f64 / 1_000_000_000.0;
    let average = rtt.iter().sum::<u128>() as f64 / rtt.len() as f64 / 1_000_000_000.0;

    log::debug!("result:");
    log::debug!("  num_heavy       = {num_heavy}");
    log::debug!("  is_heavy        = {is_heavy}");
    log::debug!("  worst case      = {worst} [s]");
    log::debug!("  99th percentile = {p99} [s]");
    log::debug!("  90th percentile = {p90} [s]");
    log::debug!("  50th percentile = {p50} [s]");
    log::debug!("  average         = {average} [s]");

    MeasureResult {
        num_task: NUM_TASK,
        num_heavy,
        is_heavy,
        worst,
        p99,
        p90,
        p50,
        average,
    }
}

async fn client_task(
    tx1: bounded::Sender<bool>,
    rx2: bounded::Receiver<bool>,
    is_heavy: bool,
    is_finished: Arc<AtomicBool>,
    mut barrier_end: Barrier,
) -> (bool, alloc::vec::Vec<u128>) {
    let mut result = alloc::vec::Vec::with_capacity(NUM_TRIAL);

    let mut n = 0;
    for _ in 0..NUM_TRIAL {
        let data = if is_heavy && is_finished.load(core::sync::atomic::Ordering::Relaxed) {
            true
        } else {
            false
        };

        let start = uptime_nano();
        tx1.send(data).await.unwrap();
        let _ = rx2.recv().await.unwrap();
        let end = uptime_nano();

        if start <= end {
            let elapsed = end - start;
            result.push(elapsed);
        }

        n += 1;

        if data {
            break;
        }
    }

    if is_heavy {
        result.truncate(n);
    } else {
        barrier_end.wait().await;
        is_finished.store(true, core::sync::atomic::Ordering::Relaxed);
    }

    (is_heavy, result)
}
