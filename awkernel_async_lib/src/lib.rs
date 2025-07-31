//! # awkernel_async_lib: Asynchronous library for Awkernel
//!
//! Awkernel is an operating system, and this is an asynchronous library.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod accepter;
pub mod action;
mod anydict;
pub mod channel;
pub mod dag;
pub mod file;
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
pub mod utils;
mod yield_task;

#[cfg(test)]
pub(crate) mod mini_task;

use crate::scheduler::SchedulerType;
use alloc::borrow::Cow;
use core::time::Duration;
use futures::{channel::oneshot, Future};
use join_handle::JoinHandle;

#[doc(hidden)]
pub use awkernel_futures_macro::select_internal;

pub use futures::select_biased;

pub use awkernel_lib::{
    cpu::cpu_id,
    delay::{cpu_counter, uptime, uptime_nano},
};

use pubsub::{
    Attribute, MultipleReceiver, MultipleSender, VectorToPublishers, VectorToSubscribers,
};

#[doc(hidden)]
pub use futures_util as __futures_crate;

/// Polls multiple futures and streams simultaneously, executing the branch
/// for the future that finishes first. If multiple futures are ready,
/// one will be pseudo-randomly selected at runtime. Futures directly
/// passed to `select!` must be `Unpin` and implement `FusedFuture`.
///
/// If an expression which yields a `Future` is passed to `select!`
/// (e.g. an `async fn` call) instead of a `Future` by name the `Unpin`
/// requirement is relaxed, since the macro will pin the resulting `Future`
/// on the stack. However the `Future` returned by the expression must
/// still implement `FusedFuture`.
///
/// Futures and streams which are not already fused can be fused using the
/// `.fuse()` method. Note, though, that fusing a future or stream directly
/// in the call to `select!` will not be enough to prevent it from being
/// polled after completion if the `select!` call is in a loop, so when
/// `select!`ing in a loop, users should take care to `fuse()` outside of
/// the loop.
///
/// `select!` can be used as an expression and will return the return
/// value of the selected branch. For this reason the return type of every
/// branch in a `select!` must be the same.
///
/// This macro is only usable inside of async functions, closures, and blocks.
/// It is also gated behind the `async-await` feature of this library, which is
/// activated by default.
///
/// # Examples
///
/// ```
/// use awkernel_async_lib::{future::FutureExt, select};
///
/// async fn select_example() {
///     select! {
///         a = async { 1 }.fuse() => a,
///         b = async { 2 }.fuse() => b
///     };
/// }
/// ```
#[macro_export]
macro_rules! select {
    ($($tokens:tt)*) => {{
        use $crate::__futures_crate as __futures_crate;
        $crate::select_internal! {
            $( $tokens )*
        }
    }}
}

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
///         SchedulerType::PrioritizedFIFO(31), // Scheduler type.
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
