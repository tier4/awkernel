//! Bounded channel.
//!
//! ```
//! use awkernel_async_lib::channel::bounded;
//!
//! let (tx, rx) = bounded::new::<u64>(Default::default());
//!
//! let _ = async move {
//!     tx.send(10).await.unwrap();
//! };
//!
//! let _ = async move {
//!     rx.recv().await.unwrap();
//! };
//! ```

use crate::{pubsub::Lifespan, r#yield};
use alloc::sync::Arc;
use awkernel_async_lib_verified::ringq::RingQ;
use awkernel_lib::{
    delay::uptime,
    sync::mutex::{MCSNode, Mutex},
};
use core::task::{Poll, Waker};
use futures::Future;
use pin_project::pin_project;

/// Channel attribute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    /// Queue size.
    pub queue_size: usize,

    /// Enable flow control.
    pub flow_control: bool,

    /// Indicate the lifespan of a message.
    pub lifespan: Lifespan,
}

/// Channel.
struct Channel<T> {
    queue: RingQ<ChannelData<T>>,
    waker_receiver: Option<Waker>,
    waker_sender: Option<Waker>,
    terminated: bool,
    attribute: Attribute,
}

impl<T> Channel<T> {
    #[inline]
    fn garbage_collect(&mut self) {
        if let Lifespan::Span(dur) = self.attribute.lifespan {
            let now = uptime();

            while let Some(data) = self.queue.head() {
                if now < data.time_stamp {
                    break;
                }

                if now - data.time_stamp >= dur.as_micros() as u64 {
                    // Too old data.
                    let _ = self.queue.pop();
                } else {
                    break;
                }
            }
        }
    }
}

struct ChannelData<T> {
    time_stamp: u64,
    data: T,
}

pub struct Receiver<T: Send> {
    chan: Arc<Mutex<Channel<T>>>,
}

pub struct Sender<T: Send> {
    chan: Arc<Mutex<Channel<T>>>,
}

/// Create a bounded single producer and single consumer channel.
///
/// # Example
///
/// ```
/// use awkernel_async_lib::channel::bounded;
///
/// let (tx, rx) = bounded::new::<u64>(Default::default());
///
/// let _ = async move { tx.send(10).await.unwrap(); };
/// let _ = async move { rx.recv().await.unwrap(); };
/// ```
pub fn new<T: Send>(attribute: Attribute) -> (Sender<T>, Receiver<T>) {
    let queue = RingQ::new(attribute.queue_size);

    let chan = Channel {
        queue,
        waker_receiver: None,
        waker_sender: None,
        terminated: false,
        attribute,
    };

    let chan = Arc::new(Mutex::new(chan));
    let sender = Sender { chan: chan.clone() };
    let receiver = Receiver { chan };

    (sender, receiver)
}

impl<T: Send> Sender<T> {
    /// Send data.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_async_lib::channel::bounded::Sender;
    ///
    /// async fn sender_task(sender: Sender<u64>) {
    ///     sender.send(123).await.unwrap();
    /// }
    /// ```
    #[inline]
    pub async fn send(&self, data: T) -> Result<(), SendErr> {
        let data = ChannelData {
            time_stamp: uptime(),
            data,
        };

        let sender = AsyncSender {
            sender: self,
            data: Some(data),
        };

        match sender.await {
            Ok(need_yield) => {
                if need_yield {
                    r#yield().await;
                }

                Ok(())
            }
            Err(err) => Err(err),
        }
    }

    #[inline]
    pub fn is_full(&self) -> bool {
        let mut node = MCSNode::new();
        let chan = self.chan.lock(&mut node);
        chan.queue.is_full()
    }

    /// Try to send data.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_async_lib::channel::bounded::Sender;
    ///
    /// fn send_example(sender: Sender<u64>) {
    ///     sender.try_send(123).unwrap();
    /// }
    /// ```
    #[inline]
    pub fn try_send(&self, data: T) -> Result<(), SendErr> {
        let data = ChannelData {
            time_stamp: uptime(),
            data,
        };

        let mut node = MCSNode::new();
        let mut chan = self.chan.lock(&mut node);

        if chan.terminated {
            return Err(SendErr::ChannelClosed);
        }

        chan.garbage_collect();

        if chan.queue.is_full() {
            if chan.attribute.flow_control {
                return Err(SendErr::Full);
            } else {
                let _ = chan.queue.pop();
            }
        }

        assert!(matches!(chan.queue.push(data), Ok(())));

        if let Some(waker_receiver) = chan.waker_receiver.take() {
            waker_receiver.wake();
        }

        Ok(())
    }

    #[inline]
    pub fn is_terminated(&self) -> bool {
        let mut node = MCSNode::new();
        let chan = self.chan.lock(&mut node);
        chan.terminated
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SendErr {
    ChannelClosed,
    Full,
}

#[pin_project]
struct AsyncSender<'a, T: Send> {
    sender: &'a Sender<T>,
    data: Option<ChannelData<T>>,
}

impl<T: Send> Future for AsyncSender<'_, T> {
    type Output = Result<bool, SendErr>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> Poll<Self::Output> {
        let this = self.project();

        let mut node = MCSNode::new();
        let mut chan = this.sender.chan.lock(&mut node);

        if chan.terminated {
            return Poll::Ready(Err(SendErr::ChannelClosed));
        }

        chan.garbage_collect();

        if chan.queue.is_full() {
            if chan.attribute.flow_control {
                chan.waker_sender = Some(cx.waker().clone());
                return Poll::Pending;
            } else {
                let _ = chan.queue.pop();
            }
        }

        if let Some(waker_receiver) = chan.waker_receiver.take() {
            waker_receiver.wake();
        }

        let data = this.data.take().unwrap();
        assert!(matches!(chan.queue.push(data), Ok(())));

        let need_yield = (chan.queue.queue_size() >> 2) < chan.queue.len();

        Poll::Ready(Ok(need_yield))
    }
}

impl<T: Send> Drop for Sender<T> {
    fn drop(&mut self) {
        let mut node = MCSNode::new();
        let mut chan = self.chan.lock(&mut node);

        chan.terminated = true;
        chan.waker_sender = None;

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

impl<T: Send> Receiver<T> {
    /// Receive data.
    /// If there is no data in the queue,
    /// the task will await data arrival.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_async_lib::channel::bounded::Receiver;
    ///
    /// async fn receiver_task(receiver: Receiver<u64>) {
    ///     let data = receiver.recv().await.unwrap();
    /// }
    /// ```
    #[inline]
    pub async fn recv(&self) -> Result<T, RecvErr> {
        let receiver = AsyncReceiver { receiver: self };
        receiver.await
    }

    /// Try to receive data.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_async_lib::channel::bounded::Receiver;
    ///
    /// fn receiver_task(receiver: Receiver<u64>) {
    ///     let data = receiver.try_recv().unwrap();
    /// }
    /// ```
    #[inline]
    pub fn try_recv(&self) -> Result<T, RecvErr> {
        let mut node = MCSNode::new();
        let mut chan = self.chan.lock(&mut node);

        chan.garbage_collect();

        if let Some(data) = chan.queue.pop() {
            Ok(data.data)
        } else if chan.terminated {
            Err(RecvErr::ChannelClosed)
        } else {
            Err(RecvErr::NoData)
        }
    }

    #[inline]
    pub fn is_terminated(&self) -> bool {
        let mut node = MCSNode::new();
        let chan = self.chan.lock(&mut node);
        chan.terminated
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

        chan.garbage_collect();

        if let Some(data) = chan.queue.pop() {
            if let Some(waker) = chan.waker_sender.take() {
                waker.wake();
            }

            Poll::Ready(Ok(data.data))
        } else if chan.terminated {
            Poll::Ready(Err(RecvErr::ChannelClosed))
        } else {
            chan.waker_receiver = Some(cx.waker().clone());
            Poll::Pending
        }
    }
}

impl<T: Send> Drop for Receiver<T> {
    fn drop(&mut self) {
        let mut node = MCSNode::new();
        let mut chan = self.chan.lock(&mut node);

        chan.terminated = true;
        chan.waker_receiver = None;

        if let Some(waker) = chan.waker_sender.take() {
            waker.wake();
        }
    }
}

impl Default for Attribute {
    /// The default value of `Attribute`.
    ///
    /// ```
    /// use awkernel_async_lib::{channel::bounded::Attribute, pubsub::Lifespan};
    ///
    /// // Default value.
    /// Attribute {
    ///     queue_size: 10,
    ///     flow_control: true,
    ///     lifespan: Lifespan::Permanent,
    /// };
    /// ```
    fn default() -> Self {
        Self {
            queue_size: 10,
            flow_control: true,
            lifespan: Lifespan::Permanent,
        }
    }
}
