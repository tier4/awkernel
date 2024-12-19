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
            self.rx.clone().recv().await;
            BarrierWaitResult(false)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::sync::Arc;
    use core::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn test_simple_async_barrier() {
        let barrier = Arc::new(Barrier::new(10));
        let num_waits = Arc::new(AtomicUsize::new(0));
        let num_leaders = Arc::new(AtomicUsize::new(0));
        let tasks = crate::mini_task::Tasks::new();

        for _ in 0..10 {
            let barrier = barrier.clone();
            let num_waits = num_waits.clone();
            let num_leaders = num_leaders.clone();
            let task = async move {
                num_waits.fetch_add(1, Ordering::Relaxed);
                if barrier.wait().await.is_reader() {
                    num_leaders.fetch_add(1, Ordering::Relaxed);
                }
                assert_eq!(num_waits.load(Ordering::Relaxed), 10);
            };
            tasks.spawn(task);
        }
        tasks.run();

        assert_eq!(num_leaders.load(Ordering::Relaxed), 1);
    }
}
