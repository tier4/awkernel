use alloc::{collections::VecDeque, sync::Arc};
use core::task::{Poll, Waker};
pub use futures::channel::*;
use futures::Future;
use synctools::mcs::{MCSLock, MCSNode};

use crate::r#yield;

struct Channel<T> {
    queue: VecDeque<T>,
    waker_receiver: Option<Waker>,
    terminated: bool,
}

pub struct Sender<T> {
    chan: Arc<MCSLock<Channel<T>>>,
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        Self {
            chan: self.chan.clone(),
        }
    }
}

impl<T> Sender<T> {
    pub async fn send(&self, data: T) -> Result<(), &'static str> {
        {
            let mut node = MCSNode::new();
            let mut chan = self.chan.lock(&mut node);

            if chan.terminated {
                return Err("Connection closed");
            }

            chan.queue.push_back(data);
        }

        r#yield().await;
        Ok(())
    }

    pub fn is_terminated(&self) -> bool {
        let mut node = MCSNode::new();
        let chan = self.chan.lock(&mut node);
        chan.terminated
    }
}

impl<T> Drop for Sender<T> {
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

pub struct Receiver<T> {
    chan: Arc<MCSLock<Channel<T>>>,
}

impl<T> Receiver<T> {
    pub async fn recv(&self) -> Result<T, RecvErr> {
        let receiver = AsyncReceiver { receiver: self };
        receiver.await
    }

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

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        let mut node = MCSNode::new();
        let mut chan = self.chan.lock(&mut node);
        chan.terminated = true;
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

pub fn unbounded<T>() -> (Sender<T>, Receiver<T>) {
    let chan = Channel {
        queue: Default::default(),
        waker_receiver: None,
        terminated: false,
    };

    let chan = Arc::new(MCSLock::new(chan));

    let sender = Sender { chan: chan.clone() };
    let receiver = Receiver { chan };

    (sender, receiver)
}

unsafe impl<T> Send for Receiver<T> {}
unsafe impl<T> Send for Sender<T> {}
