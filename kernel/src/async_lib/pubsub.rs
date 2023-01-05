use alloc::{collections::BTreeMap, sync::Arc, vec::Vec};
use core::{marker::PhantomData, task::Waker};
use futures::Future;
use synctools::mcs::MCSLock;

// pub struct Publisher<T> {}

#[derive(Clone)]
pub struct Publisher<T> {
    subscribers: Subscribers<T>,
}

#[derive(Clone)]
pub struct Subscriber<T> {
    inner: Arc<MCSLock<InnerSubscriber<T>>>,
    subscribers: Subscribers<T>,
}

struct InnerSubscriber<T> {
    ringq: RingQ<T>,
    waker: Option<Waker>,
}

#[derive(Clone)]
struct Subscribers<T> {
    id_to_subscriber: Arc<MCSLock<BTreeMap<u64, Arc<MCSLock<InnerSubscriber<T>>>>>>,
}

struct RingQ<T> {
    queue: Vec<Option<T>>,
    start: usize,
    end: usize,
    size: usize,
    max: usize,
    _phantom: PhantomData<T>,
}

impl<T> RingQ<T> {
    fn new(len: usize) -> Self {
        let mut queue = Vec::new();
        queue.resize_with(len, || None);

        Self {
            queue,
            start: 0,
            end: 0,
            size: 0,
            max: len,
            _phantom: Default::default(),
        }
    }

    fn push(&mut self, data: T) -> Result<(), T> {
        if self.size == self.max {
            return Err(data);
        }

        self.queue[self.end] = Some(data);
        self.end += 1;
        self.size += 1;

        if self.end >= self.max {
            self.end = 0;
        }

        Ok(())
    }

    fn pop(&mut self) -> Option<T> {
        if self.size == 0 {
            return None;
        }

        let result = self.queue[self.start].take();
        self.start += 1;
        self.size -= 1;

        if self.start >= self.max {
            self.start = 0;
        }

        result
    }
}

impl<T> Future for Subscriber<T> {
    type Output = T;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        todo!()
    }
}
