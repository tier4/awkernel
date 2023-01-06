use super::anydict::{AnyDict, AnyDictResult};
use alloc::{
    borrow::Cow,
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

pub struct Publisher<T: 'static> {
    subscribers: Subscribers<T>,
}

pub struct Subscriber<T: 'static> {
    inner: Arc<InnerSubscriber<T>>,
    subscribers: Subscribers<T>,
}

#[derive(Clone)]
struct Subscribers<T> {
    id_to_subscriber: Arc<RwLock<BTreeMap<usize, Arc<InnerSubscriber<T>>>>>,
    name: Cow<'static, str>,
    attribute: Attribute,
}

impl<T> Subscribers<T> {
    fn new(name: Cow<'static, str>, attribute: Attribute) -> Self {
        Self {
            id_to_subscriber: Arc::new(RwLock::new(Default::default())),
            name,
            attribute,
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
struct Receiver<'a, T: 'static> {
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
        destroy_subscriber::<T>(self);
    }
}

impl<T> Drop for Publisher<T> {
    fn drop(&mut self) {
        destroy_publisher(self);
    }
}

pin_project! {
    #[must_use = "use `.await` to send"]
    struct Sender<'a, T: 'static> {
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
    let attribute = Attribute {
        queue_size,
        durability: Durability::Volatile,
    };

    let subscribers = Subscribers::new("test".into(), attribute.clone());
    let inner_subscriber = Arc::new(InnerSubscriber::new(attribute.queue_size));

    {
        let mut guard = subscribers.id_to_subscriber.write();
        guard.insert(inner_subscriber.id(), inner_subscriber.clone());
    }

    let subscriber = Subscriber {
        inner: inner_subscriber,
        subscribers: Subscribers {
            id_to_subscriber: subscribers.id_to_subscriber.clone(),
            name: subscribers.name.clone(),
            attribute: subscribers.attribute.clone(),
        },
    };

    let publisher = Publisher { subscribers };

    (publisher, subscriber)
}

impl<T> Clone for Subscriber<T> {
    fn clone(&self) -> Self {
        let inner = Arc::new(InnerSubscriber::new(self.subscribers.attribute.queue_size));

        let mut guard = self.subscribers.id_to_subscriber.write();
        guard.insert(inner.id(), inner.clone());

        Self {
            inner,
            subscribers: Subscribers {
                id_to_subscriber: self.subscribers.id_to_subscriber.clone(),
                name: self.subscribers.name.clone(),
                attribute: self.subscribers.attribute.clone(),
            },
        }
    }
}

static PUBLISH_SUBSCRIBE: MCSLock<PubSub> = MCSLock::new(PubSub::new());

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    queue_size: usize,
    durability: Durability,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Durability {
    Volatile,
    TransientLocal,
}

#[derive(Clone)]
struct InnerPubSub<T> {
    subscribers: Subscribers<T>,
    num_publisher: u64,
}

struct PubSub {
    name_to_inner: AnyDict,
}

impl PubSub {
    const fn new() -> Self {
        Self {
            name_to_inner: AnyDict::new(),
        }
    }

    fn create_publisher<T: 'static>(
        &mut self,
        name: Cow<'static, str>,
        attribute: Attribute,
    ) -> Result<Publisher<T>, &'static str> {
        match self.name_to_inner.get_mut::<InnerPubSub<T>>(&name) {
            AnyDictResult::TypeError => Err("typing error"),
            AnyDictResult::None => {
                let subscribers = Subscribers::new(name.clone(), attribute.clone());
                let subscribers2 = Subscribers {
                    id_to_subscriber: subscribers.id_to_subscriber.clone(),
                    name: name.clone(),
                    attribute,
                };

                let inner = InnerPubSub {
                    subscribers: subscribers2,
                    num_publisher: 0,
                };

                self.name_to_inner.insert::<InnerPubSub<T>>(name, inner);

                Ok(Publisher { subscribers })
            }
            AnyDictResult::Ok(inner) => {
                if inner.subscribers.attribute == attribute {
                    inner.num_publisher += 1;

                    Ok(Publisher {
                        subscribers: Subscribers {
                            id_to_subscriber: inner.subscribers.id_to_subscriber.clone(),
                            name: inner.subscribers.name.clone(),
                            attribute,
                        },
                    })
                } else {
                    Err("incompatible attribute")
                }
            }
        }
    }

    fn create_subscriber<T: 'static>(
        &mut self,
        name: Cow<'static, str>,
        attribute: Attribute,
    ) -> Result<Subscriber<T>, &'static str> {
        match self.name_to_inner.get::<InnerPubSub<T>>(&name) {
            AnyDictResult::TypeError => Err("typing error"),
            AnyDictResult::None => {
                // Create `Subscribers`.
                let subscribers = Subscribers::new(name.clone(), attribute.clone());

                // Create `InnerSubscriber`.
                let inner_sub = Arc::new(InnerSubscriber::new(attribute.queue_size));
                {
                    let mut guard = subscribers.id_to_subscriber.write();
                    guard.insert(inner_sub.id(), inner_sub.clone());
                }

                let subscribers2 = Subscribers {
                    id_to_subscriber: subscribers.id_to_subscriber.clone(),
                    name: name.clone(),
                    attribute: attribute.clone(),
                };

                // Create `InnerPubSub`.
                let inner_pubsub = InnerPubSub {
                    subscribers: subscribers2,
                    num_publisher: 0,
                };

                self.name_to_inner
                    .insert::<InnerPubSub<T>>(name, inner_pubsub);

                // Create `Subscriber` and return it.
                Ok(Subscriber {
                    inner: inner_sub,
                    subscribers,
                })
            }
            AnyDictResult::Ok(inner) => {
                if inner.subscribers.attribute == attribute {
                    // Create `InnerSubscriber`.
                    let inner_sub = Arc::new(InnerSubscriber::new(attribute.queue_size));
                    {
                        let mut guard = inner.subscribers.id_to_subscriber.write();
                        guard.insert(inner_sub.id(), inner_sub.clone());
                    }

                    // Create `Subscriber` and return it.
                    Ok(Subscriber {
                        inner: inner_sub,
                        subscribers: Subscribers {
                            id_to_subscriber: inner.subscribers.id_to_subscriber.clone(),
                            name: inner.subscribers.name.clone(),
                            attribute: inner.subscribers.attribute.clone(),
                        },
                    })
                } else {
                    Err("incompatible attribute")
                }
            }
        }
    }

    fn destroy_publisher<T: 'static>(&mut self, publisher: &Publisher<T>) {
        match self
            .name_to_inner
            .get_mut::<InnerPubSub<T>>(&publisher.subscribers.name)
        {
            AnyDictResult::None | AnyDictResult::TypeError => (),
            AnyDictResult::Ok(inner) => {
                inner.num_publisher -= 1;
                if inner.num_publisher == 0 {
                    let guard = inner.subscribers.id_to_subscriber.read();
                    if guard.is_empty() {
                        guard.unlock();
                        self.name_to_inner.remove(&publisher.subscribers.name);
                    }
                }
            }
        }
    }

    fn destroy_subscriber<T: 'static>(&mut self, subscriber: &mut Subscriber<T>) {
        subscriber.inner.closed.store(true, Ordering::Release);

        {
            let mut guard = subscriber.inner.waker_publishers.lock();
            while let Some(waker) = guard.pop_front() {
                waker.wake();
            }
        }

        {
            let mut guard = subscriber.subscribers.id_to_subscriber.write();
            guard.remove(&subscriber.id());
        }

        match self
            .name_to_inner
            .get_mut::<InnerPubSub<T>>(&subscriber.subscribers.name)
        {
            AnyDictResult::None | AnyDictResult::TypeError => (),
            AnyDictResult::Ok(inner) => {
                if inner.num_publisher == 0 {
                    let guard = inner.subscribers.id_to_subscriber.read();
                    if guard.is_empty() {
                        guard.unlock();
                        self.name_to_inner.remove(&subscriber.subscribers.name);
                    }
                }
            }
        }
    }
}

pub fn create_publisher<T: 'static>(
    name: Cow<'static, str>,
    attribute: Attribute,
) -> Result<Publisher<T>, &'static str> {
    let mut guard = PUBLISH_SUBSCRIBE.lock();
    guard.create_publisher(name, attribute)
}

pub fn create_subscriber<T: 'static>(
    name: Cow<'static, str>,
    attribute: Attribute,
) -> Result<Subscriber<T>, &'static str> {
    let mut guard = PUBLISH_SUBSCRIBE.lock();
    guard.create_subscriber(name, attribute)
}

fn destroy_publisher<T: 'static>(publisher: &Publisher<T>) {
    let mut guard = PUBLISH_SUBSCRIBE.lock();
    guard.destroy_publisher(publisher);
}

fn destroy_subscriber<T: 'static>(subscriber: &mut Subscriber<T>) {
    let mut guard = PUBLISH_SUBSCRIBE.lock();
    guard.destroy_subscriber(subscriber);
}

impl Attribute {
    pub fn new(queue_size: usize, durability: Durability) -> Self {
        Self {
            queue_size,
            durability,
        }
    }
}
