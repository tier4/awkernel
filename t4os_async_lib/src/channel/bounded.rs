use crate::{pubsub::Lifespan, r#yield, ringq::RingQ};
use alloc::sync::Arc;
use core::task::{Poll, Waker};
use futures::Future;
use pin_project_lite::pin_project;
use synctools::mcs::{MCSLock, MCSNode};
use t4os_lib::delay::uptime;

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
    fn garbage_collect(&mut self) {
        if let Lifespan::Span(dur) = self.attribute.lifespan {
            let now = uptime();

            while let Some(data) = self.queue.head() {
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

pub struct Receiver<T> {
    chan: Arc<MCSLock<Channel<T>>>,
}

pub struct Sender<T> {
    chan: Arc<MCSLock<Channel<T>>>,
}

pub fn new<T>(attribute: Attribute) -> (Sender<T>, Receiver<T>) {
    let queue = RingQ::new(attribute.queue_size);

    let chan = Channel {
        queue,
        waker_receiver: None,
        waker_sender: None,
        terminated: false,
        attribute,
    };

    let chan = Arc::new(MCSLock::new(chan));
    let sender = Sender { chan: chan.clone() };
    let receiver = Receiver { chan };

    (sender, receiver)
}

impl<T: Send> Sender<T> {
    pub async fn send(&self, data: T) -> Result<(), SendErr> {
        let data = ChannelData {
            time_stamp: uptime(),
            data,
        };

        let sender = AsyncSender {
            sender: self,
            data: Some(data),
        };

        let result = sender.await;
        r#yield().await;
        result
    }

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

        Ok(())
    }

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

pin_project! {
    struct AsyncSender<'a, T> {
        sender: &'a Sender<T>,
        data: Option<ChannelData<T>>,
    }
}

impl<'a, T> Future for AsyncSender<'a, T> {
    type Output = Result<(), SendErr>;

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

        let data = this.data.take().unwrap();
        assert!(matches!(chan.queue.push(data), Ok(())));

        Poll::Ready(Ok(()))
    }
}

impl<T> Drop for Sender<T> {
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

impl<T> Receiver<T> {
    pub async fn recv(&self) -> Result<T, RecvErr> {
        let receiver = AsyncReceiver { receiver: self };
        receiver.await
    }

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

    pub fn is_terminated(&self) -> bool {
        let mut node = MCSNode::new();
        let chan = self.chan.lock(&mut node);
        chan.terminated
    }
}

struct AsyncReceiver<'a, T> {
    receiver: &'a Receiver<T>,
}

impl<'a, T> Future for AsyncReceiver<'a, T> {
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

impl<T> Drop for Receiver<T> {
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
    /// use t4os_async_lib::{channel::bounded::Attribute, pubsub::Lifespan};
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
