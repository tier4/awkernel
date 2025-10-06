//! Publish and subscribe communication.
//!
//! # Example
//!
//! ```
//! use core::time::Duration;
//! use awkernel_async_lib::{pubsub::{create_publisher, create_subscriber, Attribute}, sleep};
//!
//! let publisher = create_publisher::<u64>("rendezvous name".into(), Attribute::default()).unwrap();
//! let subscriber = create_subscriber::<u64>("rendezvous name".into(), Attribute::default()).unwrap();
//!
//! // Publisher task.
//! let _ = async move {
//!     let mut i = 0;
//!     loop {
//!         publisher.send(i).await;
//!         i += 1;
//!         sleep(Duration::from_secs(1)).await;
//!     }
//! };
//!
//! // Subscriber task.
//! let _ = async move {
//!     loop {
//!         let data = subscriber.recv().await;
//!     }
//! };
//! ```

use super::{
    anydict::{AnyDict, AnyDictResult},
    r#yield,
};

use alloc::{
    borrow::Cow,
    boxed::Box,
    collections::{BTreeMap, VecDeque},
    sync::Arc,
    vec::Vec,
};
use awkernel_async_lib_verified::ringq::RingQ;
use awkernel_lib::sync::{
    mutex::{MCSNode, Mutex},
    rwlock::RwLock,
};
use core::{
    pin::Pin,
    task::{Poll, Waker},
    time::Duration,
};
use futures::Future;
use pin_project::pin_project;

/// Data and timestamp.
#[derive(Clone)]
pub struct Data<T> {
    pub timestamp: awkernel_lib::time::Time,
    pub data: T,
}

/// Publisher.
pub struct Publisher<T: 'static + Send> {
    subscribers: Subscribers<T>,
}

/// Subscriber.
pub struct Subscriber<T: 'static + Clone + Send> {
    inner: ArcInner<T>,
    subscribers: Subscribers<T>,
}

struct Subscribers<T: Send> {
    id_to_subscriber: Arc<RwLock<BTreeMap<usize, ArcInner<T>>>>,
    name: Cow<'static, str>,
    sender_buf: Option<Arc<Mutex<RingQ<Data<T>>>>>,
    attribute: Attribute,
}

impl<T: Send> Subscribers<T> {
    fn new(name: Cow<'static, str>, attribute: Attribute) -> Self {
        let sender_buf = if attribute.transient_local {
            Some(Arc::new(Mutex::new(RingQ::new(attribute.queue_size))))
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

/// Subscriber.
impl<T: Send> Clone for Subscribers<T> {
    fn clone(&self) -> Self {
        Self {
            id_to_subscriber: self.id_to_subscriber.clone(),
            name: self.name.clone(),
            sender_buf: self.sender_buf.clone(),
            attribute: self.attribute.clone(),
        }
    }
}

fn inner_id<T: Send>(inner: &ArcInner<T>) -> usize {
    inner.as_ref() as *const _ as _
}

struct InnerSubscriber<T> {
    queue: RingQ<Data<T>>,
    waker_publishers: VecDeque<Waker>,
    waker_subscriber: Option<Waker>,
    closed: bool,
}

type ArcInner<T> = Arc<Mutex<InnerSubscriber<T>>>;

impl<T> InnerSubscriber<T> {
    fn new(queue_size: usize) -> Self {
        Self {
            queue: RingQ::new(queue_size),
            waker_publishers: Default::default(),
            waker_subscriber: None,
            closed: false,
        }
    }

    fn garbage_collect(&mut self, lifespan: &Lifespan) {
        if let Lifespan::Span(lifespan) = lifespan {
            let span = lifespan.as_micros();
            while let Some(head) = self.queue.head() {
                if head.timestamp.elapsed().as_micros() > span {
                    self.queue.pop();
                } else {
                    break;
                }
            }
        }
    }
}

#[must_use = "use `.await` to receive"]
struct Receiver<'a, T: 'static + Clone + Send> {
    subscriber: &'a Subscriber<T>,
}

impl<T: Clone + Send> Future for Receiver<'_, T> {
    type Output = Data<T>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        self.subscriber.poll_recv(cx)
    }
}

impl<T: Clone + Send> Subscriber<T> {
    /// Receive data asynchronously.
    pub async fn recv(&self) -> Data<T> {
        let receiver = Receiver { subscriber: self };
        receiver.await
    }

    pub(super) fn poll_recv(&self, cx: &mut core::task::Context<'_>) -> core::task::Poll<Data<T>> {
        let mut node = MCSNode::new();
        let mut inner = self.inner.lock(&mut node);

        inner.garbage_collect(&self.subscribers.attribute.lifespan);

        if let Some(data) = inner.queue.pop() {
            for _ in 0..inner.queue.queue_size() - inner.queue.len() {
                if let Some(waker) = inner.waker_publishers.pop_front() {
                    waker.wake();
                } else {
                    break;
                }
            }
            core::task::Poll::Ready(data)
        } else {
            inner.waker_subscriber = Some(cx.waker().clone());
            core::task::Poll::Pending
        }
    }

    /// Non-blocking data receive.
    /// If there is no data, return `None`.
    pub fn try_recv(&self) -> Option<Data<T>> {
        let mut node = MCSNode::new();
        let mut inner = self.inner.lock(&mut node);

        inner.garbage_collect(&self.subscribers.attribute.lifespan);

        let result = inner.queue.pop();

        for _ in 0..inner.queue.queue_size() - inner.queue.len() {
            if let Some(waker) = inner.waker_publishers.pop_front() {
                waker.wake();
            } else {
                break;
            }
        }

        result
    }

    fn id(&self) -> usize {
        inner_id(&self.inner)
    }
}

impl<T: Clone + Send> Drop for Subscriber<T> {
    fn drop(&mut self) {
        destroy_subscriber::<T>(self);
    }
}

impl<T: Send> Drop for Publisher<T> {
    fn drop(&mut self) {
        destroy_publisher(self);
    }
}

#[must_use = "use `.await` to send"]
#[pin_project]
struct Sender<'a, T: 'static + Send> {
    publisher: &'a Publisher<T>,
    data: Option<T>,
    subscribers: VecDeque<ArcInner<T>>,
    state: SenderState,
    timestamp: awkernel_lib::time::Time,
}

enum SenderState {
    Start,
    Wait,
    Finished,
}

impl<'a, T: Send> Sender<'a, T> {
    pub(super) fn new(publisher: &'a Publisher<T>, data: T) -> Self {
        Self {
            publisher,
            data: Some(data),
            subscribers: Default::default(),
            state: SenderState::Start,
            timestamp: awkernel_lib::time::Time::now(),
        }
    }
}

impl<T> Future for Sender<'_, T>
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
                        // Store data to the send buffer.
                        if let Some(buf) = &this.publisher.subscribers.sender_buf {
                            let mut node = MCSNode::new();
                            let mut guard = buf.lock(&mut node);
                            if let Err(data) = guard.push(Data {
                                timestamp: awkernel_lib::time::Time::now(),
                                data: data.clone(),
                            }) {
                                // If the send buffer is full, then remove the oldest one and store again.
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
                            drop(inner);

                            this.subscribers.push_front(subscriber);
                            return Poll::Pending;
                        }

                        inner.garbage_collect(&this.publisher.subscribers.attribute.lifespan);

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
                                    drop(inner);

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

/// Create an anonymous publisher and an anonymous subscriber.
/// This channel works as a channel of multiple producers and multiple consumers.
///
/// # Example
///
/// ```
/// use awkernel_async_lib::pubsub::{create_pubsub, Attribute};
///
/// let _ = async {
///     let (publisher, subscriber) = create_pubsub(Attribute::default());
///     publisher.send(10).await;
///     let data = subscriber.recv().await;
/// };
/// ```
pub fn create_pubsub<T: Clone + Send>(attribute: Attribute) -> (Publisher<T>, Subscriber<T>) {
    let subscribers = Subscribers::new("anonymous".into(), attribute.clone());
    let inner = Arc::new(Mutex::new(InnerSubscriber::new(attribute.queue_size)));

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

impl<T: Clone + Send> Clone for Subscriber<T> {
    fn clone(&self) -> Self {
        let inner = Arc::new(Mutex::new(InnerSubscriber::new(
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

static PUBLISH_SUBSCRIBE: Mutex<PubSub> = Mutex::new(PubSub::new());

/// Channel attribute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    /// Queue size.
    pub queue_size: usize,

    /// If `flow_control` is `true` and a subscriber's queue is full,
    /// a publisher will block until the queue is not full.
    /// It is good for reliability, but bad for real-time.
    ///
    /// If `flow_control` is `false` and a subscriber's queue is full,
    /// the oldest message will discarded and pushed the new message to the queue.
    /// It is good for real-time, but bad for reliability.
    pub flow_control: bool,

    /// Store messages when publishing, and late joining subscribers can receive the latest messages.
    pub transient_local: bool,

    /// Indicate the lifespan of a message.
    pub lifespan: Lifespan,
}

/// Lifespan of a message.
///
/// `Lifespan` represent how log a message is valid.
/// `Lifespan::Permanent` means messages are valid forever.
/// `Lifespan::Span(Duration)` means messages will be expired and discarded after the span of `Duration`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lifespan {
    Permanent,
    Span(Duration),
}

#[derive(Clone)]
struct InnerPubSub<T: Send> {
    subscribers: Subscribers<T>,
    num_publisher: u64,
}

/// Manager of publishers and subscribers.
struct PubSub {
    name_to_inner: AnyDict,
}

impl PubSub {
    const fn new() -> Self {
        Self {
            name_to_inner: AnyDict::new(),
        }
    }

    fn create_publisher<T: 'static + Send>(
        &mut self,
        name: Cow<'static, str>,
        attribute: Attribute,
    ) -> Result<Publisher<T>, &'static str> {
        match self.name_to_inner.get_mut::<InnerPubSub<T>>(&name) {
            AnyDictResult::TypeError => Err("create_publisher: typing error"),
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
                    Err("create_publisher: incompatible attribute")
                }
            }
        }
    }

    fn create_subscriber<T: 'static + Clone + Send>(
        &mut self,
        name: Cow<'static, str>,
        attribute: Attribute,
    ) -> Result<Subscriber<T>, &'static str> {
        match self.name_to_inner.get::<InnerPubSub<T>>(&name) {
            AnyDictResult::TypeError => Err("create_subscriber: typing error"),
            AnyDictResult::None => {
                // Create `Subscribers`.
                let subscribers = Subscribers::new(name.clone(), attribute.clone());

                // Create `InnerSubscriber`.
                let inner_sub = Arc::new(Mutex::new(InnerSubscriber::new(attribute.queue_size)));
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

                    let inner_sub = Arc::new(Mutex::new(inner_sub));

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
                    Err("create_subscriber: incompatible attribute")
                }
            }
        }
    }

    fn destroy_publisher<T: 'static + Send>(&mut self, publisher: &Publisher<T>) {
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

    fn destroy_subscriber<T: 'static + Clone + Send>(&mut self, subscriber: &Subscriber<T>) {
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

/// Create a publisher.
///
/// # Example
///
/// ```
/// use awkernel_async_lib::pubsub::{create_publisher, Attribute};
///
/// let _ = async {
///     let publisher = create_publisher("rendezvous name".into(), Attribute::default()).unwrap();
///     publisher.send(100).await;
/// };
/// ```
pub fn create_publisher<T: 'static + Send>(
    name: Cow<'static, str>,
    attribute: Attribute,
) -> Result<Publisher<T>, &'static str> {
    let mut node = MCSNode::new();
    let mut guard = PUBLISH_SUBSCRIBE.lock(&mut node);
    guard.create_publisher(name, attribute)
}

/// Create a subscriber.
///
/// # Example
///
/// ```
/// use awkernel_async_lib::pubsub::{create_subscriber, Attribute};
///
/// let _ = async {
///     let subscriber = create_subscriber::<u64>("rendezvous name".into(), Attribute::default()).unwrap();
///     let data = subscriber.recv().await;
/// };
/// ```
pub fn create_subscriber<T: 'static + Clone + Send>(
    name: Cow<'static, str>,
    attribute: Attribute,
) -> Result<Subscriber<T>, &'static str> {
    let mut node = MCSNode::new();
    let mut guard = PUBLISH_SUBSCRIBE.lock(&mut node);
    guard.create_subscriber(name, attribute)
}

/// Destroy a publisher.
fn destroy_publisher<T: 'static + Send>(publisher: &Publisher<T>) {
    let mut node = MCSNode::new();
    let mut guard = PUBLISH_SUBSCRIBE.lock(&mut node);
    guard.destroy_publisher(publisher);
}

/// Destroy a subscriber.
fn destroy_subscriber<T: 'static + Clone + Send>(subscriber: &Subscriber<T>) {
    let mut node = MCSNode::new();
    let mut guard = PUBLISH_SUBSCRIBE.lock(&mut node);
    guard.destroy_subscriber(subscriber);
}

impl Attribute {
    /// Create a new attribute.
    pub fn new(
        queue_size: usize,
        flow_control: bool,
        transient_local: bool,
        lifespan: Lifespan,
    ) -> Self {
        Self {
            queue_size,
            flow_control,
            transient_local,
            lifespan,
        }
    }
}

impl Default for Attribute {
    /// The default value of `Attribute`.
    ///
    /// ```
    /// use awkernel_async_lib::pubsub::{Attribute, Lifespan};
    ///
    /// // Default value.
    /// Attribute {
    ///     queue_size: 10,
    ///     flow_control: true,
    ///     transient_local: false,
    ///     lifespan: Lifespan::Permanent,
    /// };
    /// ```
    fn default() -> Self {
        Self {
            queue_size: 10,
            flow_control: true,
            transient_local: false,
            lifespan: Lifespan::Permanent,
        }
    }
}

pub trait MultipleReceiver {
    type Item;

    fn recv_all(&self) -> Pin<Box<dyn Future<Output = Self::Item> + Send + '_>>;
}

pub trait MultipleSender {
    type Item;

    fn send_all(&self, item: Self::Item) -> Pin<Box<dyn Future<Output = ()> + Send + '_>>;
}
pub trait VectorToPublishers {
    type Publishers: MultipleSender;

    fn create_publishers(topics: Vec<Cow<'static, str>>, attribute: Attribute) -> Self::Publishers;
}

pub trait VectorToSubscribers {
    type Subscribers: MultipleReceiver;

    fn create_subscribers(
        topics: Vec<Cow<'static, str>>,
        attribute: Attribute,
    ) -> Self::Subscribers;
}

macro_rules! impl_tuple_to_pub_sub {
    () => {
        impl VectorToPublishers for () {
            type Publishers = ();

            fn create_publishers(_topics: Vec<Cow<'static, str>>, _attribute: Attribute) -> Self::Publishers {
            }
        }

        impl VectorToSubscribers for () {
            type Subscribers = ();

            fn create_subscribers(_topics: Vec<Cow<'static, str>>, _attribute: Attribute) -> Self::Subscribers {
            }
        }
    };
    ($($T:ident),+) => {
        impl<$($T: 'static + Send + Sync + Clone,)+> VectorToPublishers for ($($T,)+)
        {
            type Publishers = ($(Publisher<$T>,)+);

            fn create_publishers(topics: Vec<Cow<'static, str>>, attribute: Attribute) -> Self::Publishers {
                let mut topics = topics.into_iter();
                ($(
                    create_publisher::<$T>(topics.next().unwrap(), attribute.clone()).unwrap(),
                )+)
            }
        }

        impl<$($T: 'static + Clone + Send,)+> VectorToSubscribers for ($($T,)+)
        {
            type Subscribers = ($(Subscriber<$T>,)+);

            fn create_subscribers(topics: Vec<Cow<'static, str>>, attribute: Attribute) -> Self::Subscribers {
                let mut topics = topics.into_iter();
                ($(
                    create_subscriber::<$T>(topics.next().unwrap(), attribute.clone()).unwrap(),
                )+)
            }
        }
    }
}

impl_tuple_to_pub_sub!();
impl_tuple_to_pub_sub!(A);
impl_tuple_to_pub_sub!(A, B);
impl_tuple_to_pub_sub!(A, B, C);
impl_tuple_to_pub_sub!(T0, T1, T2, T3);
impl_tuple_to_pub_sub!(T0, T1, T2, T3, T4);
impl_tuple_to_pub_sub!(T0, T1, T2, T3, T4, T5);
impl_tuple_to_pub_sub!(T0, T1, T2, T3, T4, T5, T6);
impl_tuple_to_pub_sub!(T0, T1, T2, T3, T4, T5, T6, T7);

macro_rules! impl_async_receiver_for_tuple {
    () => {
        impl MultipleReceiver for () {
            type Item = ();

            fn recv_all(&self) -> Pin<Box<dyn Future<Output = Self::Item> + Send + '_>> {
                Box::pin(async move{})
            }
        }

        impl MultipleSender for () {
            type Item = ();

            fn send_all(&self, _item: Self::Item) -> Pin<Box<dyn Future<Output = ()> + Send + '_>> {
                Box::pin(async move{})
            }
        }
    };
    ($(($T:ident, $idx:tt, $idx2:tt)),+) => {
        impl<$($T: Clone + Send + 'static),*> MultipleReceiver for ($(Subscriber<$T>,)*) {
            type Item = ($($T,)+);

            fn recv_all(&self) -> Pin<Box<dyn Future<Output = Self::Item> + Send + '_>> {
                let ($($idx,)+) = self;
                Box::pin(async move {
                    ($($idx.recv().await.data,)+)
                })
            }
        }

        impl<$($T: Clone + Sync + Send + 'static),+> MultipleSender for ($(Publisher<$T>,)+) {
            type Item = ($($T,)+);

            fn send_all(&self, item: Self::Item) -> Pin<Box<dyn Future<Output = ()> + Send + '_>> {
                let ($($idx,)+) = self;
                let ($($idx2,)+) = item;
                Box::pin(async move {
                    $(
                        $idx.send($idx2).await;
                    )+
                })
            }
        }
    };
}

impl_async_receiver_for_tuple!();
impl_async_receiver_for_tuple!((A, a, p));
impl_async_receiver_for_tuple!((A, a, p), (B, b, q));
impl_async_receiver_for_tuple!((A, a, p), (B, b, q), (C, c, r));
impl_async_receiver_for_tuple!((T0, v0, p0), (T1, v1, p1), (T2, v2, p2), (T3, v3, p3));
impl_async_receiver_for_tuple!(
    (T0, v0, p0),
    (T1, v1, p1),
    (T2, v2, p2),
    (T3, v3, p3),
    (T4, v4, p4)
);
impl_async_receiver_for_tuple!(
    (T0, v0, p0),
    (T1, v1, p1),
    (T2, v2, p2),
    (T3, v3, p3),
    (T4, v4, p4),
    (T5, v5, p5)
);
impl_async_receiver_for_tuple!(
    (T0, v0, p0),
    (T1, v1, p1),
    (T2, v2, p2),
    (T3, v3, p3),
    (T4, v4, p4),
    (T5, v5, p5),
    (T6, v6, p6)
);
impl_async_receiver_for_tuple!(
    (T0, v0, p0),
    (T1, v1, p1),
    (T2, v2, p2),
    (T3, v3, p3),
    (T4, v4, p4),
    (T5, v5, p5),
    (T6, v6, p6),
    (T7, v7, p7)
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pubsub() {
        let (tx, rx) = create_pubsub::<u64>(Attribute::default());

        let task1 = async move {
            for i in 0..10 {
                tx.send(i).await;
            }
        };

        let rx2 = rx.clone();

        let task2 = async move {
            for _ in 0..10 {
                rx2.recv().await;
            }
        };

        let task3 = async move {
            for _ in 0..10 {
                rx.recv().await;
            }
        };

        let tasks = crate::mini_task::Tasks::new();
        tasks.spawn(task1);
        tasks.spawn(task2);
        tasks.spawn(task3);

        tasks.run();
    }

    #[test]
    fn test_transient_local() {
        let mut attribute = Attribute::default();
        attribute.transient_local = true;

        let (tx, rx) = create_pubsub::<u64>(attribute);

        let task1 = async move {
            for i in 0..10 {
                tx.send(i).await;
            }
        };

        let rx2 = rx.clone();

        let task2 = async move {
            for n in 0..10 {
                let m = rx2.recv().await;
                assert_eq!(n, m.data);
            }
        };

        let tasks = crate::mini_task::Tasks::new();
        tasks.spawn(task1);
        tasks.spawn(task2);

        tasks.run();

        let task3 = async move {
            for n in 0..10 {
                let m = rx.recv().await;
                assert_eq!(n, m.data);
            }
        };

        tasks.spawn(task3);
        tasks.run();
    }
}
