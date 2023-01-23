use crate::delay::uptime;

use super::{
    anydict::{AnyDict, AnyDictResult},
    r#yield,
    ringq::RingQ,
};
use alloc::{
    borrow::Cow,
    collections::{BTreeMap, VecDeque},
    sync::Arc,
};
use core::task::{Poll, Waker};
use futures::Future;
use pin_project_lite::pin_project;
use synctools::{
    mcs::{MCSLock, MCSNode},
    rwlock::RwLock,
};

#[derive(Clone)]
pub struct Data<T> {
    pub timestamp: u64,
    pub data: T,
}

pub struct Publisher<T: 'static> {
    subscribers: Subscribers<T>,
}

pub struct Subscriber<T: 'static + Clone> {
    inner: ArcInner<T>,
    subscribers: Subscribers<T>,
}

struct Subscribers<T> {
    id_to_subscriber: Arc<RwLock<BTreeMap<usize, ArcInner<T>>>>,
    name: Cow<'static, str>,
    sender_buf: Option<Arc<MCSLock<RingQ<Data<T>>>>>,
    attribute: Attribute,
}

impl<T> Subscribers<T> {
    fn new(name: Cow<'static, str>, attribute: Attribute) -> Self {
        let sender_buf = if attribute.transient_local {
            Some(Arc::new(MCSLock::new(RingQ::new(attribute.queue_size))))
        } else {
            None
        };

        Self {
            id_to_subscriber: Arc::new(RwLock::new(Default::default())),
            name,
            sender_buf,
            attribute,
        }
    }
}

impl<T> Clone for Subscribers<T> {
    fn clone(&self) -> Self {
        Self {
            id_to_subscriber: self.id_to_subscriber.clone(),
            name: self.name.clone(),
            sender_buf: self.sender_buf.clone(),
            attribute: self.attribute.clone(),
        }
    }
}

fn inner_id<T>(inner: &ArcInner<T>) -> usize {
    inner.as_ref() as *const _ as _
}

struct InnerSubscriber<T> {
    queue: RingQ<Data<T>>,
    waker_publishers: VecDeque<Waker>,
    waker_subscriber: Option<Waker>,
    closed: bool,
}

type ArcInner<T> = Arc<MCSLock<InnerSubscriber<T>>>;

impl<T> InnerSubscriber<T> {
    fn new(queue_size: usize) -> Self {
        Self {
            queue: RingQ::new(queue_size),
            waker_publishers: Default::default(),
            waker_subscriber: None,
            closed: false,
        }
    }
}

#[must_use = "use `.await` to receive"]
struct Receiver<'a, T: 'static + Clone> {
    subscriber: &'a Subscriber<T>,
}

impl<'a, T: Clone> Future for Receiver<'a, T> {
    type Output = Data<T>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let mut node = MCSNode::new();
        let mut inner = self.subscriber.inner.lock(&mut node);

        if let Some(waker) = inner.waker_publishers.pop_front() {
            waker.wake();
        }

        if let Some(data) = inner.queue.pop() {
            Poll::Ready(data)
        } else {
            inner.waker_subscriber = Some(cx.waker().clone());
            Poll::Pending
        }
    }
}

impl<T: Clone> Subscriber<T> {
    pub async fn recv(&self) -> Data<T> {
        let receiver = Receiver { subscriber: self };
        receiver.await
    }

    fn id(&self) -> usize {
        inner_id(&self.inner)
    }
}

impl<T: Clone> Drop for Subscriber<T> {
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
        subscribers: VecDeque<ArcInner<T>>,
        state: SenderState,
        timestamp: u64,
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
            timestamp: uptime(),
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

                    if this.publisher.subscribers.attribute.transient_local {
                        if let Some(buf) = &this.publisher.subscribers.sender_buf {
                            let mut node = MCSNode::new();
                            let mut guard = buf.lock(&mut node);
                            if let Err(data) = guard.push(Data {
                                timestamp: uptime(),
                                data: data.clone(),
                            }) {
                                guard.pop();
                                let _ = guard.push(data);
                            }
                        }
                    }

                    *this.state = SenderState::Wait;
                }
                SenderState::Wait => {
                    while let Some(subscriber) = this.subscribers.pop_front() {
                        let mut node = MCSNode::new();
                        let mut inner = subscriber.lock(&mut node);

                        if inner.closed {
                            continue;
                        }

                        if !inner.waker_publishers.is_empty() {
                            // If there are other publishers waiting send, enqueue itself to `waker_publishers`,
                            inner.waker_publishers.push_back(cx.waker().clone());
                            inner.unlock();

                            this.subscribers.push_front(subscriber);
                            return Poll::Pending;
                        }

                        match inner.queue.push(Data {
                            timestamp: *this.timestamp,
                            data: data.clone(),
                        }) {
                            Ok(_) => {
                                // Wake the subscriber up.
                                if let Some(waker) = inner.waker_subscriber.take() {
                                    waker.wake();
                                }
                            }
                            Err(data) => {
                                if this.publisher.subscribers.attribute.flow_control {
                                    // If there are no room in the queue to send data, enqueue itself to `waker_publishers`.
                                    inner.waker_publishers.push_back(cx.waker().clone());
                                    inner.unlock();

                                    this.subscribers.push_front(subscriber);
                                    return Poll::Pending;
                                } else {
                                    // If there are no room in the queue, remove the oldest one.
                                    inner.queue.pop();
                                    let _ = inner.queue.push(data);
                                }
                            }
                        }
                    }

                    if this.subscribers.is_empty() {
                        *this.state = SenderState::Finished;
                        return Poll::Ready(());
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
        r#yield().await;
    }
}

pub fn create_pubsub<T: Clone>(
    queue_size: usize,
    flow_control: bool,
    transient_local: bool,
) -> (Publisher<T>, Subscriber<T>) {
    let attribute = Attribute {
        queue_size,
        flow_control,
        transient_local,
    };

    let subscribers = Subscribers::new("anonymous".into(), attribute.clone());
    let inner = Arc::new(MCSLock::new(InnerSubscriber::new(attribute.queue_size)));

    {
        let mut guard = subscribers.id_to_subscriber.write();
        guard.insert(inner_id(&inner), inner.clone());
    }

    let subscriber = Subscriber {
        inner,
        subscribers: subscribers.clone(),
    };

    let publisher = Publisher { subscribers };

    (publisher, subscriber)
}

impl<T: Clone> Clone for Subscriber<T> {
    fn clone(&self) -> Self {
        let inner = Arc::new(MCSLock::new(InnerSubscriber::new(
            self.subscribers.attribute.queue_size,
        )));

        let mut guard = self.subscribers.id_to_subscriber.write();
        guard.insert(inner_id(&inner), inner.clone());

        Self {
            inner,
            subscribers: self.subscribers.clone(),
        }
    }
}

static PUBLISH_SUBSCRIBE: MCSLock<PubSub> = MCSLock::new(PubSub::new());

/// Channel attribute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    /// Queue size.
    queue_size: usize,

    /// If `flow_control` is `true` and a subscriber's queue is full,
    /// a publisher will block until the queue is not full.
    /// It is good for reliability, but bad for real-time.
    ///
    /// If `flow_control` is `false` and a subscriber's queue is full,
    /// the oldest message will discarded and pushed the new message to the queue.
    /// It is good for real-time, but bad for reliability.
    flow_control: bool,

    /// Store messages when publishing, and late joining subscribers can receive the latest messages.
    transient_local: bool,
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
                    sender_buf: subscribers.sender_buf.clone(),
                    attribute,
                };

                let inner = InnerPubSub {
                    subscribers: subscribers2,
                    num_publisher: 1,
                };

                self.name_to_inner.insert::<InnerPubSub<T>>(name, inner);

                Ok(Publisher { subscribers })
            }
            AnyDictResult::Ok(inner) => {
                if inner.subscribers.attribute == attribute {
                    inner.num_publisher += 1;

                    Ok(Publisher {
                        subscribers: inner.subscribers.clone(),
                    })
                } else {
                    Err("incompatible attribute")
                }
            }
        }
    }

    fn create_subscriber<T: 'static + Clone>(
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
                let inner_sub = Arc::new(MCSLock::new(InnerSubscriber::new(attribute.queue_size)));
                {
                    let mut guard = subscribers.id_to_subscriber.write();
                    guard.insert(inner_id(&inner_sub), inner_sub.clone());
                }

                let subscribers2 = subscribers.clone();

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
                    let mut inner_sub = InnerSubscriber::new(attribute.queue_size);

                    // Insert sent data to the queue.
                    if attribute.transient_local {
                        if let Some(buf) = &inner.subscribers.sender_buf {
                            let mut node = MCSNode::new();
                            let guard = buf.lock(&mut node);
                            for data in guard.iter() {
                                let _ = inner_sub.queue.push(data.clone());
                            }
                        }
                    }

                    let inner_sub = Arc::new(MCSLock::new(inner_sub));

                    {
                        let mut guard = inner.subscribers.id_to_subscriber.write();
                        guard.insert(inner_id(&inner_sub), inner_sub.clone());
                    }

                    // Create `Subscriber` and return it.
                    Ok(Subscriber {
                        inner: inner_sub,
                        subscribers: inner.subscribers.clone(),
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

    fn destroy_subscriber<T: 'static + Clone>(&mut self, subscriber: &mut Subscriber<T>) {
        {
            let mut guard = subscriber.subscribers.id_to_subscriber.write();
            guard.remove(&subscriber.id());
        }

        {
            let mut node = MCSNode::new();
            let mut inner = subscriber.inner.lock(&mut node);

            // Close.
            inner.closed = true;

            // Wake all publishers up.
            while let Some(waker) = inner.waker_publishers.pop_front() {
                waker.wake();
            }
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
    let mut node = MCSNode::new();
    let mut guard = PUBLISH_SUBSCRIBE.lock(&mut node);
    guard.create_publisher(name, attribute)
}

pub fn create_subscriber<T: 'static + Clone>(
    name: Cow<'static, str>,
    attribute: Attribute,
) -> Result<Subscriber<T>, &'static str> {
    let mut node = MCSNode::new();
    let mut guard = PUBLISH_SUBSCRIBE.lock(&mut node);
    guard.create_subscriber(name, attribute)
}

fn destroy_publisher<T: 'static>(publisher: &Publisher<T>) {
    let mut node = MCSNode::new();
    let mut guard = PUBLISH_SUBSCRIBE.lock(&mut node);
    guard.destroy_publisher(publisher);
}

fn destroy_subscriber<T: 'static + Clone>(subscriber: &mut Subscriber<T>) {
    let mut node = MCSNode::new();
    let mut guard = PUBLISH_SUBSCRIBE.lock(&mut node);
    guard.destroy_subscriber(subscriber);
}

impl Attribute {
    pub fn new(queue_size: usize, flow_control: bool, transient_local: bool) -> Self {
        Self {
            queue_size,
            flow_control,
            transient_local,
        }
    }
}

impl Default for Attribute {
    fn default() -> Self {
        Self {
            queue_size: 10,
            flow_control: true,
            transient_local: false,
        }
    }
}
