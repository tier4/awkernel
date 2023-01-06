use alloc::{
    collections::{BTreeMap, VecDeque},
    sync::Arc,
};
use core::{
    sync::atomic::{AtomicBool, Ordering},
    task::{Poll, Waker},
};
use crossbeam_queue::ArrayQueue;
use futures::Future;
use pin_project_lite::pin_project;
use synctools::{mcs::MCSLock, rwlock::RwLock};

pub struct Publisher<T> {
    subscribers: Subscribers<T>,
}

pub struct Subscriber<T> {
    inner: Arc<InnerSubscriber<T>>,
    subscribers: Subscribers<T>,
}

#[derive(Clone)]
struct Subscribers<T> {
    id_to_subscriber: Arc<RwLock<BTreeMap<usize, Arc<InnerSubscriber<T>>>>>,
}

impl<T> Subscribers<T> {
    fn new() -> Self {
        Self {
            id_to_subscriber: Arc::new(RwLock::new(Default::default())),
        }
    }
}

struct InnerSubscriber<T> {
    queue: ArrayQueue<T>,
    waker_publishers: MCSLock<VecDeque<Waker>>,
    waker_subscriber: MCSLock<Option<Waker>>,
    closed: AtomicBool,
}

impl<T> InnerSubscriber<T> {
    fn new(queue_size: usize) -> Self {
        Self {
            queue: ArrayQueue::new(queue_size),
            waker_publishers: MCSLock::new(Default::default()),
            waker_subscriber: MCSLock::new(None),
            closed: AtomicBool::new(false),
        }
    }

    fn id(self: &Arc<Self>) -> usize {
        self.as_ref() as *const _ as usize
    }
}

#[must_use = "use `.await` to receive"]
struct Receiver<'a, T> {
    subscriber: &'a Subscriber<T>,
}

impl<'a, T> Future for Receiver<'a, T> {
    type Output = T;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let inner = &self.subscriber.inner;

        if let Some(data) = inner.queue.pop() {
            return Poll::Ready(data);
        }

        let mut guard = inner.waker_subscriber.lock();
        if let Some(data) = inner.queue.pop() {
            Poll::Ready(data)
        } else {
            *guard = Some(cx.waker().clone());
            Poll::Pending
        }
    }
}

impl<T> Subscriber<T> {
    pub async fn recv(&self) -> T {
        let receiver = Receiver { subscriber: self };
        receiver.await
    }

    fn id(&self) -> usize {
        self.inner.id()
    }
}

impl<T> Drop for Subscriber<T> {
    fn drop(&mut self) {
        self.inner.closed.store(true, Ordering::SeqCst);

        let mut guard = self.inner.waker_publishers.lock();
        while let Some(waker) = guard.pop_front() {
            waker.wake();
        }

        let mut guard = self.subscribers.id_to_subscriber.write();
        guard.remove(&self.id());
    }
}

pin_project! {
    #[must_use = "use `.await` to send"]
    struct Sender<'a, T> {
        publisher: &'a Publisher<T>,
        data: Option<T>,
        subscribers: VecDeque<Arc<InnerSubscriber<T>>>,
        state: SenderState
    }
}

enum SenderState {
    Start,
    Wait,
    Finished,
}

impl<'a, T> Sender<'a, T> {
    pub(super) fn new(publisher: &'a Publisher<T>, data: T) -> Self {
        Self {
            publisher,
            data: Some(data),
            subscribers: Default::default(),
            state: SenderState::Start,
        }
    }
}

impl<'a, T> Future for Sender<'a, T>
where
    T: Clone + Sync + Send,
{
    type Output = ();

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> Poll<Self::Output> {
        let this = self.project();
        let data = this.data.clone().unwrap();

        loop {
            match &this.state {
                SenderState::Start => {
                    let guard = this.publisher.subscribers.id_to_subscriber.read();
                    for x in guard.values() {
                        this.subscribers.push_back(x.clone());
                    }

                    *this.state = SenderState::Wait;
                }
                SenderState::Wait => {
                    while let Some(subscriber) = this.subscribers.pop_front() {
                        if subscriber.closed.load(Ordering::Acquire) {
                            continue;
                        }

                        {
                            let mut guard = subscriber.waker_publishers.lock();
                            if !guard.is_empty() {
                                // If there are other publishers waiting send, enqueue itself to `waker_publishers`,
                                guard.push_back(cx.waker().clone());
                                guard.unlock();

                                this.subscribers.push_front(subscriber);
                                return Poll::Pending;
                            }
                        }

                        match subscriber.queue.push(data.clone()) {
                            Ok(_) => {
                                // Wake the subscriber up.
                                let mut guard = subscriber.waker_subscriber.lock();
                                if let Some(waker) = guard.take() {
                                    waker.wake();
                                }
                            }
                            Err(_) => {
                                // If there are no room in the queue to send data, enqueue itself to `waker_publishers`.
                                let mut guard = subscriber.waker_publishers.lock();
                                guard.push_back(cx.waker().clone());
                                guard.unlock();

                                this.subscribers.push_front(subscriber);
                                return Poll::Pending;
                            }
                        }
                    }

                    if this.subscribers.is_empty() {
                        *this.state = SenderState::Finished;
                        return Poll::Ready(());
                    } else {
                        return Poll::Pending;
                    }
                }
                SenderState::Finished => return Poll::Ready(()),
            }
        }
    }
}

impl<T> Publisher<T>
where
    T: Clone + Sync + Send,
{
    pub async fn send(&self, data: T) {
        let sender = Sender::new(self, data);
        sender.await;
    }
}

pub fn create_pubsub<T>(queue_size: usize) -> (Publisher<T>, Subscriber<T>) {
    let subscribers = Subscribers::new();
    let inner_subscriber = Arc::new(InnerSubscriber::new(queue_size));

    {
        let mut guard = subscribers.id_to_subscriber.write();
        guard.insert(inner_subscriber.id(), inner_subscriber.clone());
    }

    let subscriber = Subscriber {
        inner: inner_subscriber,
        subscribers: Subscribers {
            id_to_subscriber: subscribers.id_to_subscriber.clone(),
        },
    };

    let publisher = Publisher { subscribers };

    (publisher, subscriber)
}

impl<T> Clone for Subscriber<T> {
    fn clone(&self) -> Self {
        let inner = Arc::new(InnerSubscriber::new(self.inner.queue.capacity()));

        let mut guard = self.subscribers.id_to_subscriber.write();
        guard.insert(inner.id(), inner.clone());

        Self {
            inner,
            subscribers: Subscribers {
                id_to_subscriber: self.subscribers.id_to_subscriber.clone(),
            },
        }
    }
}
