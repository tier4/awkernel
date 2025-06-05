//! Unbounded channel.
//!
//! # Example
//!
//! ## Unbounded Single Producer and Single Consumer Channel
//!
//! ```
//! use awkernel_async_lib::channel::unbounded;
//!
//! let (tx, rx) = unbounded::new();
//!
//! let _ = async move {
//!     for i in 0..10 {
//!         tx.send(i).await.unwrap();
//!     }
//! };
//!
//! let _ = async move {
//!     for _ in 0..10 {
//!         rx.recv().await.unwrap();
//!     }
//! };
//! ```

use crate::r#yield;
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::task::{Poll, Waker};
use futures::Future;

/// Channel.
struct Channel<T> {
    queue: VecDeque<T>,
    waker_receiver: Option<Waker>,
    terminated: bool,
}

/// Sender of a channel.
pub struct Sender<T: Send> {
    chan: Arc<Mutex<Channel<T>>>,
}

impl<T: Send> Clone for Sender<T> {
    fn clone(&self) -> Self {
        Self {
            chan: self.chan.clone(),
        }
    }
}

impl<T: Send> Sender<T> {
    /// Send data.
    /// A task will yield automatically after sending data.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_async_lib::channel::unbounded::Sender;
    ///
    /// async fn sender_task(sender: Sender<u64>) {
    ///     sender.send(123).await.unwrap();
    /// }
    /// ```
    pub async fn send(&self, data: T) -> Result<(), &'static str> {
        self.send_no_yield(data)?;
        r#yield().await;
        Ok(())
    }

    pub(crate) fn send_no_yield(&self, data: T) -> Result<(), &'static str> {
        {
            let mut node = MCSNode::new();
            let mut chan = self.chan.lock(&mut node);

            if chan.terminated {
                return Err("Connection closed");
            }

            chan.queue.push_back(data);

            if let Some(waker_receiver) = chan.waker_receiver.take() {
                waker_receiver.wake();
            }
        }

        Ok(())
    }

    pub fn is_terminated(&self) -> bool {
        let mut node = MCSNode::new();
        let chan = self.chan.lock(&mut node);
        chan.terminated
    }
}

impl<T: Send> Drop for Sender<T> {
    fn drop(&mut self) {
        let mut node = MCSNode::new();
        let mut chan = self.chan.lock(&mut node);
        chan.terminated = true;
        if let Some(waker) = chan.waker_receiver.take() {
            waker.wake();
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum RecvErr {
    ChannelClosed,
    NoData,
}

/// Receiver of a channel.
pub struct Receiver<T: Send> {
    chan: Arc<Mutex<Channel<T>>>,
}

impl<T: Send> Receiver<T> {
    /// Receive data.
    /// If there is no data in the queue,
    /// the task will await data arrival.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_async_lib::channel::unbounded::Receiver;
    ///
    /// async fn receiver_task(receiver: Receiver<u64>) {
    ///     let data = receiver.recv().await.unwrap();
    /// }
    /// ```
    pub async fn recv(&self) -> Result<T, RecvErr> {
        let receiver = AsyncReceiver { receiver: self };
        receiver.await
    }

    /// Try to receive data.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_async_lib::channel::unbounded::Receiver;
    ///
    /// fn receiver_task(receiver: Receiver<u64>) {
    ///     let data = receiver.try_recv().unwrap();
    /// }
    /// ```
    pub fn try_recv(&self) -> Result<T, RecvErr> {
        let mut node = MCSNode::new();
        let mut chan = self.chan.lock(&mut node);
        if let Some(e) = chan.queue.pop_front() {
            Ok(e)
        } else if chan.terminated {
            Err(RecvErr::ChannelClosed)
        } else {
            Err(RecvErr::NoData)
        }
    }
}

impl<T: Send> Drop for Receiver<T> {
    fn drop(&mut self) {
        let mut node = MCSNode::new();
        let mut chan = self.chan.lock(&mut node);
        chan.terminated = true;
    }
}

struct AsyncReceiver<'a, T: Send> {
    receiver: &'a Receiver<T>,
}

impl<T: Send> Future for AsyncReceiver<'_, T> {
    type Output = Result<T, RecvErr>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let mut node = MCSNode::new();
        let mut chan = self.receiver.chan.lock(&mut node);

        if let Some(data) = chan.queue.pop_front() {
            Poll::Ready(Ok(data))
        } else if chan.terminated {
            Poll::Ready(Err(RecvErr::ChannelClosed))
        } else {
            chan.waker_receiver = Some(cx.waker().clone());
            Poll::Pending
        }
    }
}

/// Create a unbounded single producer and single consumer channel.
///
/// # Example
///
/// ```
/// use awkernel_async_lib::channel::unbounded;
///
/// let (tx, rx) = unbounded::new::<u64>();
///
/// let _ = async move { tx.send(10).await.unwrap(); };
/// let _ = async move { rx.recv().await.unwrap(); };
/// ```
pub fn new<T: Send>() -> (Sender<T>, Receiver<T>) {
    let chan = Channel {
        queue: Default::default(),
        waker_receiver: None,
        terminated: false,
    };

    let chan = Arc::new(Mutex::new(chan));

    let sender = Sender { chan: chan.clone() };
    let receiver = Receiver { chan };

    (sender, receiver)
}

unsafe impl<T: Send> Send for Receiver<T> {}
unsafe impl<T: Send> Send for Sender<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_channel() {
        let (tx, rx) = new();

        let task1 = async move {
            for i in 0..10 {
                tx.send(i).await.unwrap();
            }
        };

        let task2 = async move {
            for _ in 0..10 {
                rx.recv().await.unwrap();
            }
        };

        let tasks = crate::mini_task::Tasks::new();
        tasks.spawn(task1);
        tasks.spawn(task2);

        tasks.run();
    }
}
