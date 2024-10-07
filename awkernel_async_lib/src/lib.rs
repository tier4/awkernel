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
mod delay;
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
mod timeout_call;
mod yield_task;

#[cfg(test)]
pub(crate) mod mini_task;

use crate::pubsub::AsyncReceiver;
use crate::scheduler::SchedulerType;
use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::pin::Pin;
use core::time::Duration;
use futures::{channel::oneshot, Future};
use join_handle::JoinHandle;
use pubsub::{Attribute, Subscriber, TupleToPublishers, TupleToSubscribers};

pub use futures::select_biased;

pub use awkernel_lib::{
    cpu::cpu_id,
    delay::{cpu_counter, uptime},
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
    sleep_task::Sleep::new(duration.as_micros() as u64).await
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

/// Wait forever. Never return.
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

pub async fn spawn_reactor<F, Args, Ret>(
    reactor_name: Cow<'static, str>,
    f: F,
    subscribe_topic_names: Vec<Cow<'static, str>>,
    publish_topic_names: Vec<Cow<'static, str>>,
    sched_type: SchedulerType,
) -> Pin<Box<dyn Future<Output = ()> + Send + 'static>>
/*-> JoinHandle<T>*/
where
    F: Fn(<Args::Subscribers as AsyncReceiver>::Item) -> Ret + Send + 'static,
    Args: TupleToSubscribers,
    Ret: TupleToPublishers,
    Args::Subscribers: AsyncReceiver + 'static,
    <Args::Subscribers as AsyncReceiver>::Item: Send,
{
    let publishers =
        <Ret as TupleToPublishers>::create_publishers(publish_topic_names, Attribute::default());

    let subscribers = Arc::new(Args::create_subscribers(
        subscribe_topic_names,
        Attribute::default(),
    ));

    Box::pin(async move {
        loop {
            let args = subscribers.recv_all().await;
            let results = f(args);
            //publishers.publish_all(results).await;
        }
    })

    /*
    crate::task::spawn(
        reactor_name,
        async move {
            loop {
                for subscriber in subscribers.iter() {
                    let ret = subscriber.recv().await;
                    let _ = ret;
                }
            }
        },
        sched_type,
    );
    */
}
