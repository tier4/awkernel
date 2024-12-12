use crate::pubsub::{self, Attribute, Publisher, Subscriber};
use core::sync::atomic::AtomicUsize;

/// A barrier enables multiple threads to synchronize the beginning of some computation.
pub struct Barrier {
    count: AtomicUsize,
    tx: Publisher<()>,
    rx: Subscriber<()>,
}

/// `BarrierWaitResult` is returned by `Barrier::wait` when all threads in `Barrier` have rendezvoused.
pub struct BarrierWaitResult(bool);

impl BarrierWaitResult {
    pub fn is_reader(&self) -> bool {
        self.0
    }
}

impl Barrier {
    /// Creates a new barrier that can block a given number of threads.
    pub fn new(count: usize) -> Self {
        let attr = Attribute {
            queue_size: 1,
            ..Attribute::default()
        };
        let (tx, rx) = pubsub::create_pubsub(attr);

        Self {
            count: AtomicUsize::new(count),
            tx,
            rx,
        }
    }

    /// Blocks the current thread until all threads have redezvoused here.
    /// A single (arbitrary) thread will receive `BarrierWaitResult(true)` when returning fron this function, and other threads will receive `BarrierWaitResult(false)`.
    pub async fn wait(&self) -> BarrierWaitResult {
        if self
            .count
            .fetch_sub(1, core::sync::atomic::Ordering::Relaxed)
            == 1
        {
            self.tx.send(()).await;
            BarrierWaitResult(true)
        } else {
            self.rx.recv().await;
            BarrierWaitResult(false)
        }
    }
}
