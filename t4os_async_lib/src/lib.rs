//! # t4os_async_lib: Asynchronous library for T4OS
//!
//! T4OS is an operating system, and this is an asynchronous library
//! to provide APIs like to Robot Operating System 2 (ROS2).
//! For example, there are asynchronous APIs for publish and subscribe
//! communications.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

pub mod action;
mod anydict;
pub mod channel;
mod delay;
mod delta_list;
mod join_handle;
mod never_return;
pub mod pubsub;
mod ringq;
pub mod scheduler;
pub mod service;
pub mod session_types;
mod sleep_task;
pub mod task;
mod timeout_call;
mod yield_task;

#[cfg(test)]
pub(crate) mod mini_task;

use crate::scheduler::SchedulerType;
use core::time::Duration;
use futures::{channel::oneshot, Future};
use join_handle::JoinHandle;

pub use awkernel_lib::delay::{cpu_counter, uptime};

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
/// use t4os_async_lib::sleep;
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
/// use t4os_async_lib::r#yield;
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
/// use t4os_async_lib::{forever, timeout};
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
/// use t4os_async_lib::forever;
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
/// use t4os_async_lib::{self, scheduler::SchedulerType};
///
/// let _ = async {
///     // Spawn a detached task.
///     let join_handler = t4os_async_lib::spawn(
///         async { /* do something */ },
///         SchedulerType::RoundRobin, // Scheduler type.
///     ).await;
///
///     // Join the task, but it is not necessary.
///     let result = join_handler.join().await;
/// };
/// ```
pub async fn spawn<T>(
    future: impl Future<Output = T> + 'static + Send,
    sched_type: SchedulerType,
) -> JoinHandle<T>
where
    T: Sync + Send + 'static,
{
    let (tx, rx) = oneshot::channel();

    crate::task::spawn(
        async move {
            let result = future.await;
            let _ = tx.send(result);
            Ok(())
        },
        sched_type,
    );

    JoinHandle::new(rx)
}
