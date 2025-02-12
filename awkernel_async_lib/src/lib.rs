//! # awkernel_async_lib: Asynchronous library for Autoware Kernel
//!
//! Autoware Kernel is an operating system, and this is an asynchronous library
//! to provide APIs like to Robot Operating System 2 (ROS2).
//! For example, there are asynchronous APIs for publish and subscribe
//! communications.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod accepter;
pub mod action;
mod anydict;
pub mod channel;
pub mod dag;
pub mod future;
mod join_handle;
pub mod net;
mod never_return;
pub mod pubsub;
pub mod scheduler;
pub mod service;
pub mod session_types;
mod sleep_task;
pub mod sync;
pub mod task;
pub mod time;
mod timeout_call;
mod yield_task;

#[cfg(test)]
pub(crate) mod mini_task;

use crate::scheduler::SchedulerType;
use alloc::{borrow::Cow, vec::Vec};
use core::time::Duration;
use futures::{channel::oneshot, Future};
use join_handle::JoinHandle;

pub use futures::{select, select_biased};

pub use awkernel_lib::{
    cpu::cpu_id,
    delay::{cpu_counter, uptime, uptime_nano},
};

use pubsub::{
    Attribute, MultipleReceiver, MultipleSender, VectorToPublishers, VectorToSubscribers,
};

pub trait Cancel: Future + Unpin {
    fn cancel(self: core::pin::Pin<&mut Self>) {
        let this = self.get_mut();
        this.cancel_unpin();
    }
    fn cancel_unpin(&mut self);
}

/// Sleep `duration`.
///
/// # Example
///
/// ```
/// use core::time::Duration;
/// use awkernel_async_lib::sleep;
///
/// let _ = async {
///     // Sleep 1 second.
///     sleep(Duration::from_secs(1)).await;
/// };
/// ```
pub async fn sleep(duration: Duration) -> sleep_task::State {
    sleep_task::Sleep::new(duration).await
}

/// Yield the CPU to the next executable task.
/// Because `yield` is a reserved word of Rust,
/// `r#yield` is used here.
///
/// # Example
///
/// ```
/// use awkernel_async_lib::r#yield;
///
/// let _ = async {
///     // Yield.
///     r#yield().await;
/// };
/// ```
pub async fn r#yield() {
    yield_task::Yield::new().await
}

/// Do the `future` with a timeout.
///
/// # Example
///
/// ```
/// use core::time::Duration;
/// use awkernel_async_lib::{forever, timeout};
///
/// let _ = async {
///     // `async { forever().await; }` will time out after 1 second.
///     timeout(Duration::from_secs(1), async { forever().await; }).await;
/// };
pub async fn timeout<F, T>(duration: Duration, future: F) -> Option<T>
where
    F: Future<Output = T>,
{
    timeout_call::Timeout::new(duration, future).await
}

/// Wait forever. Never return.
///
/// # Example
///
/// ```
/// use awkernel_async_lib::forever;
///
/// let _ = async {
///     // Wait forever.
///     forever().await;
/// };
/// ```
pub async fn forever() -> ! {
    never_return::Never.await;
    unreachable!();
}

/// Spawn a detached task.
///
/// # Example
///
/// ```
/// use awkernel_async_lib::{self, scheduler::SchedulerType};
///
/// let _ = async {
///     // Spawn a detached task.
///     let join_handler = awkernel_async_lib::spawn(
///         "name".into(),
///         async { /* do something */ },
///         SchedulerType::FIFO, // Scheduler type.
///     ).await;
///
///     // Join the task, but it is not necessary.
///     let result = join_handler.join().await;
/// };
/// ```
pub async fn spawn<T>(
    name: Cow<'static, str>,
    future: impl Future<Output = T> + 'static + Send,
    sched_type: SchedulerType,
) -> JoinHandle<T>
where
    T: Sync + Send + 'static,
{
    let (tx, rx) = oneshot::channel();

    crate::task::spawn(
        name,
        async move {
            let result = future.await;
            let _ = tx.send(result);
            Ok(())
        },
        sched_type,
    );

    JoinHandle::new(rx)
}

/// Spawn a detached reactor. To spawn the reactor below, write code shown in the example.
///
/// topic1 (u32)              topic3 (u64)
///        |    +-----------+    |
///        +--->|  reactor  |--->+
///        |    +-----------+    |
/// topic2 (String)           topic4 (bool)
///
/// # Example
///
/// ```
/// extern crate alloc;
///
/// use awkernel_async_lib::{scheduler::SchedulerType, spawn_reactor};
/// use alloc::borrow::Cow;
///
/// let f = |(a, b) : (u32, String)| -> (u64, bool) { /* do something */ (0, false) };
///
/// let _ = async {
///     let _ = spawn_reactor::<_, (u32, String), (u64, bool)>(
///         "reactor".into(),
///         f,
///         vec![Cow::from("topic1"), Cow::from("topic2")],
///         vec![Cow::from("topic3"), Cow::from("topic4")],
///         SchedulerType::FIFO,
///     )
///     .await;
/// };
/// ```
pub async fn spawn_reactor<F, Args, Ret>(
    reactor_name: Cow<'static, str>,
    f: F,
    subscribe_topic_names: Vec<Cow<'static, str>>,
    publish_topic_names: Vec<Cow<'static, str>>,
    sched_type: SchedulerType,
) -> u32
where
    F: Fn(
            <Args::Subscribers as MultipleReceiver>::Item,
        ) -> <Ret::Publishers as MultipleSender>::Item
        + Send
        + 'static,
    Args: VectorToSubscribers,
    Ret: VectorToPublishers,
    Ret::Publishers: Send,
    Args::Subscribers: Send,
{
    let future = async move {
        let publishers = <Ret as VectorToPublishers>::create_publishers(
            publish_topic_names,
            Attribute::default(),
        );

        let subscribers: <Args as VectorToSubscribers>::Subscribers =
            Args::create_subscribers(subscribe_topic_names, Attribute::default());

        loop {
            let args: <<Args as VectorToSubscribers>::Subscribers as MultipleReceiver>::Item =
                subscribers.recv_all().await;
            let results = f(args);
            publishers.send_all(results).await;
        }
    };

    crate::task::spawn(reactor_name, future, sched_type)
}

pub async fn spawn_periodic_reactor<F, Ret>(
    reactor_name: Cow<'static, str>,
    f: F,
    publish_topic_names: Vec<Cow<'static, str>>,
    sched_type: SchedulerType,
    period: Duration,
) -> u32
where
    F: Fn() -> <Ret::Publishers as MultipleSender>::Item + Send + 'static,
    Ret: VectorToPublishers,
    Ret::Publishers: Send,
{
    // TODO(sykwer): Improve mechanisms to more closely align performance behavior with the DAG scheduling model.
    let future = async move {
        let publishers = <Ret as VectorToPublishers>::create_publishers(
            publish_topic_names,
            Attribute::default(),
        );

        loop {
            sleep(period).await; //TODO(sykwer):Improve the accuracy of the period.
            let results = f();
            publishers.send_all(results).await;
        }
    };

    crate::task::spawn(reactor_name, future, sched_type)
}
