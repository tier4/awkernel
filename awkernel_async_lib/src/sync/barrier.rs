use crate::pubsub::{self, Attribute, Publisher, Subscriber};
use alloc::{vec, vec::Vec};
use core::sync::atomic::AtomicUsize;

/// A barrier enables multiple threads to synchronize the beginning of some computation.
pub struct Barrier {
    count: AtomicUsize,
    num_threads: usize,
    tx: Publisher<()>,
    rxs: Vec<Subscriber<()>>,
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
    pub fn new(n: usize) -> Self {
        let attr = Attribute {
            queue_size: 1,
            ..Attribute::default()
        };
        let (tx, rx) = pubsub::create_pubsub(attr);

        let mut rxs = vec![rx.clone(); n - 2];
        rxs.push(rx);

        Self {
            num_threads: n,
            count: AtomicUsize::new(0),
            tx,
            rxs,
        }
    }

    /// Blocks the current thread until all threads have redezvoused here.
    /// A single (arbitrary) thread will receive `BarrierWaitResult(true)` when returning from this function, and other threads will receive `BarrierWaitResult(false)`.
    pub async fn wait(&self) -> BarrierWaitResult {
        let count = self
            .count
            .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        if count < self.num_threads - 1 {
            self.rxs[count].recv().await;
            BarrierWaitResult(false)
        } else {
            // Safety: count must be set to 0 before calling Sender::poll, as it switches to a task waiting to receive.
            self.count.store(0, core::sync::atomic::Ordering::Relaxed);
            self.tx.send(()).await;
            BarrierWaitResult(true)
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
                // Verify that Barrier synchronizes the specified number of threads
                assert_eq!(num_waits.load(Ordering::Relaxed), 10);

                // it is safe to call Barrier::wait again
                barrier.wait().await;
            };

            tasks.spawn(task);
        }
        tasks.run();

        // Verify that only one thread receives BarrierWaitResult(true)
        assert_eq!(num_leaders.load(Ordering::Relaxed), 1);
    }
}
