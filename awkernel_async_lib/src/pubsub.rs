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
use crate::delay::uptime;
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
use core::pin::Pin;
use core::{
    any::Any,
    task::{Poll, Waker},
    time::Duration,
};
use futures::Future;
use pin_project::pin_project;

/// Data and timestamp.
#[derive(Clone)]
pub struct Data<T> {
    pub timestamp: u64,
    pub data: T,
}

/// Publisher
pub struct Publisher<T: 'static + Send> {
    topic: InnerTopic<T>,
}

/// Subscriber.
pub struct Subscriber<T: 'static + Clone + Send> {
    inner: ArcInner<T>,
    topic: InnerTopic<T>,
}

struct InnerTopic<T: Send> {
    id_to_subscriber: Arc<RwLock<BTreeMap<usize, ArcInner<T>>>>,
    name: Cow<'static, str>,
    sender_buf: Option<Arc<Mutex<RingQ<Data<T>>>>>,
    attribute: Attribute,
}

impl<T: Send> InnerTopic<T> {
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
impl<T: Send> Clone for InnerTopic<T> {
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
                if uptime() - head.timestamp > span as u64 {
                    self.queue.pop();
                }
            }
        }
    }
}

#[must_use = "use `.await` to receive"]
struct Receiver<'a, T: 'static + Clone + Send> {
    subscriber: &'a Subscriber<T>,
}

impl<'a, T: Clone + Send> Future for Receiver<'a, T> {
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

        inner.garbage_collect(&self.subscriber.topic.attribute.lifespan);

        if let Some(data) = inner.queue.pop() {
            Poll::Ready(data)
        } else {
            inner.waker_subscriber = Some(cx.waker().clone());
            Poll::Pending
        }
    }
}

impl<T: Clone + Send> Subscriber<T> {
    pub async fn recv(&self) -> Data<T> {
        let receiver = Receiver { subscriber: self };
        receiver.await
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
    timestamp: u64,
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
                    let guard = this.publisher.topic.id_to_subscriber.read();
                    for x in guard.values() {
                        this.subscribers.push_back(x.clone());
                    }

                    if this.publisher.topic.attribute.transient_local {
                        // Store data to the send buffer.
                        if let Some(buf) = &this.publisher.topic.sender_buf {
                            let mut node = MCSNode::new();
                            let mut guard = buf.lock(&mut node);
                            if let Err(data) = guard.push(Data {
                                timestamp: uptime(),
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

                        inner.garbage_collect(&this.publisher.topic.attribute.lifespan);

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
                                if this.publisher.topic.attribute.flow_control {
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
    let subscribers = InnerTopic::new("anonymous".into(), attribute.clone());
    let inner = Arc::new(Mutex::new(InnerSubscriber::new(attribute.queue_size)));

    {
        let mut guard = subscribers.id_to_subscriber.write();
        guard.insert(inner_id(&inner), inner.clone());
    }

    let subscriber = Subscriber {
        inner,
        topic: subscribers.clone(),
    };

    let publisher = Publisher { topic: subscribers };

    (publisher, subscriber)
}

impl<T: Clone + Send> Clone for Subscriber<T> {
    fn clone(&self) -> Self {
        let inner = Arc::new(Mutex::new(InnerSubscriber::new(
            self.topic.attribute.queue_size,
        )));

        let mut guard = self.topic.id_to_subscriber.write();
        guard.insert(inner_id(&inner), inner.clone());

        Self {
            inner,
            topic: self.topic.clone(),
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

/// `Lifespan` represent how log a message is valid.
/// `Lifespan::Permanent` means messages are valid forever.
/// `Lifespan::Span(Duration)` means messages will be expired and discarded after the span of `Duration`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lifespan {
    Permanent,
    Span(Duration),
}

#[derive(Clone)]
struct Topic<T: Send> {
    inner_topic: InnerTopic<T>,
    num_publisher: u64,
}

/// Manager of publishers and subscribers.
struct PubSub {
    name_to_topic: AnyDict,
}

impl PubSub {
    const fn new() -> Self {
        Self {
            name_to_topic: AnyDict::new(),
        }
    }

    fn create_publisher<T: 'static + Send>(
        &mut self,
        name: Cow<'static, str>,
        attribute: Attribute,
    ) -> Result<Publisher<T>, &'static str> {
        match self.name_to_topic.get_mut::<Topic<T>>(&name) {
            AnyDictResult::TypeError => Err("create_publisher: typing error"),
            AnyDictResult::None => {
                let topic = InnerTopic::new(name.clone(), attribute.clone());
                let topic2 = InnerTopic {
                    id_to_subscriber: topic.id_to_subscriber.clone(),
                    name: name.clone(),
                    sender_buf: topic.sender_buf.clone(),
                    attribute,
                };

                let inner = Topic {
                    inner_topic: topic2,
                    num_publisher: 1,
                };

                self.name_to_topic.insert::<Topic<T>>(name, inner);

                Ok(Publisher { topic })
            }
            AnyDictResult::Ok(inner) => {
                if inner.inner_topic.attribute == attribute {
                    inner.num_publisher += 1;

                    Ok(Publisher {
                        topic: inner.inner_topic.clone(),
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
        match self.name_to_topic.get::<Topic<T>>(&name) {
            AnyDictResult::TypeError => Err("create_subscriber: typing error"),
            AnyDictResult::None => {
                // Create `Subscribers`.
                let topic = InnerTopic::new(name.clone(), attribute.clone());

                // Create `InnerSubscriber`.
                let inner_sub = Arc::new(Mutex::new(InnerSubscriber::new(attribute.queue_size)));
                {
                    let mut guard = topic.id_to_subscriber.write();
                    guard.insert(inner_id(&inner_sub), inner_sub.clone());
                }

                let topic2 = topic.clone();

                // Create `InnerPubSub`.
                let inner_pubsub = Topic {
                    inner_topic: topic2,
                    num_publisher: 0,
                };

                self.name_to_topic.insert::<Topic<T>>(name, inner_pubsub);

                // Create `Subscriber` and return it.
                Ok(Subscriber {
                    inner: inner_sub,
                    topic,
                })
            }
            AnyDictResult::Ok(inner) => {
                if inner.inner_topic.attribute == attribute {
                    // Create `InnerSubscriber`.
                    let mut inner_sub = InnerSubscriber::new(attribute.queue_size);

                    // Insert sent data to the queue.
                    if attribute.transient_local {
                        if let Some(buf) = &inner.inner_topic.sender_buf {
                            let mut node = MCSNode::new();
                            let guard = buf.lock(&mut node);
                            for data in guard.iter() {
                                let _ = inner_sub.queue.push(data.clone());
                            }
                        }
                    }

                    let inner_sub = Arc::new(Mutex::new(inner_sub));

                    {
                        let mut guard = inner.inner_topic.id_to_subscriber.write();
                        guard.insert(inner_id(&inner_sub), inner_sub.clone());
                    }

                    // Create `Subscriber` and return it.
                    Ok(Subscriber {
                        inner: inner_sub,
                        topic: inner.inner_topic.clone(),
                    })
                } else {
                    Err("create_subscriber: incompatible attribute")
                }
            }
        }
    }

    fn destroy_publisher<T: 'static + Send>(&mut self, publisher: &Publisher<T>) {
        match self
            .name_to_topic
            .get_mut::<Topic<T>>(&publisher.topic.name)
        {
            AnyDictResult::None | AnyDictResult::TypeError => (),
            AnyDictResult::Ok(inner) => {
                inner.num_publisher -= 1;
                if inner.num_publisher == 0 {
                    let guard = inner.inner_topic.id_to_subscriber.read();
                    if guard.is_empty() {
                        guard.unlock();
                        self.name_to_topic.remove(&publisher.topic.name);
                    }
                }
            }
        }
    }

    fn destroy_subscriber<T: 'static + Clone + Send>(&mut self, subscriber: &Subscriber<T>) {
        {
            let mut guard = subscriber.topic.id_to_subscriber.write();
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
            .name_to_topic
            .get_mut::<Topic<T>>(&subscriber.topic.name)
        {
            AnyDictResult::None | AnyDictResult::TypeError => (),
            AnyDictResult::Ok(inner) => {
                if inner.num_publisher == 0 {
                    let guard = inner.inner_topic.id_to_subscriber.read();
                    if guard.is_empty() {
                        guard.unlock();
                        self.name_to_topic.remove(&subscriber.topic.name);
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

pub trait TupleToPublishers {
    type Publishers;
    fn create_publishers(topics: Vec<Cow<'static, str>>, attribute: Attribute) -> Self::Publishers;
}

pub trait TupleToSubscribers: Send + 'static {
    type Subscribers: AsyncReceiver + 'static;
    fn create_subscribers(
        topics: Vec<Cow<'static, str>>,
        attribute: Attribute,
    ) -> Self::Subscribers;
}

pub trait AsyncReceiver: Send + Sync {
    type Item: Send;
    fn recv_all(&self) -> Pin<Box<dyn Future<Output = Self::Item> + Send + '_>>;
}

impl<T: Clone + Send + 'static> AsyncReceiver for Subscriber<T> {
    type Item = T;

    fn recv_all(&self) -> Pin<Box<dyn Future<Output = Self::Item> + Send + '_>> {
        Box::pin(async move { self.recv().await.data })
    }
}

macro_rules! impl_tuple_to_pub_sub {
    () => {
        impl TupleToPublishers for () {
            type Publishers = ();

            fn create_publishers(_topics: Vec<Cow<'static, str>>, _attribute: Attribute) -> Self::Publishers {
                ()
            }
        }

        impl TupleToSubscribers for () {
            type Subscribers = ();

            fn create_subscribers(_topics: Vec<Cow<'static, str>>, _attribute: Attribute) -> Self::Subscribers {
                ()
            }
        }
    };
    ($($T:ident),+) => {
        impl<$($T: 'static + Send,)+> TupleToPublishers for ($($T,)+)
        {
            type Publishers = ($(Publisher<$T>,)+);

            fn create_publishers(topics: Vec<Cow<'static, str>>, attribute: Attribute) -> Self::Publishers {
                let mut topics = topics.into_iter();
                ($(
                    create_publisher::<$T>(topics.next().unwrap(), attribute.clone()).unwrap(),
                )+)
            }
        }

        impl<$($T: 'static + Clone + Send,)+> TupleToSubscribers for ($($T,)+)
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
impl_tuple_to_pub_sub!(A, B, C, D);

macro_rules! impl_async_receiver_for_tuple {
    ($($T:ident),*) => {
        impl<$($T: Clone + Send + 'static),*> AsyncReceiver for ($(Subscriber<$T>,)*) {
            type Item = ($($T,)*);

            fn recv_all(&self) -> Pin<Box<dyn Future<Output = Self::Item> + Send + '_>> {
                #[allow(non_snake_case)]
                let ($($T,)*) = self;
                Box::pin(async move {
                    ($(
                        $T.recv_all().await,
                    )*)
                })
            }
        }
    };
}

impl_async_receiver_for_tuple!();
impl_async_receiver_for_tuple!(A);
impl_async_receiver_for_tuple!(A, B);
impl_async_receiver_for_tuple!(A, B, C);
impl_async_receiver_for_tuple!(A, B, C, D);

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
