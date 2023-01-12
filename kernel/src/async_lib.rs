use core::time::Duration;
use futures::{channel::oneshot, Future};

mod anydict;
pub mod never_return;
pub mod pubsub;
mod ringq;
pub mod sleep_task;
pub mod timeout_call;
pub mod yield_task;

pub use futures::channel;

use crate::scheduler::SchedulerType;

pub trait Cancel: Future + Unpin {
    fn cancel(self: core::pin::Pin<&mut Self>) {
        let this = self.get_mut();
        this.cancel_unpin();
    }
    fn cancel_unpin(&mut self);
}

pub async fn sleep(duration: Duration) -> sleep_task::State {
    sleep_task::Sleep::new(duration.as_micros() as u64).await
}

pub async fn r#yield() {
    yield_task::Yield::new().await
}

pub async fn timeout<F, T>(duration: Duration, future: F) -> Option<T>
where
    F: Future<Output = T>,
{
    timeout_call::Timeout::new(duration, future).await
}

pub async fn forever() {
    never_return::Never.await;
}

pub async fn spawn<T>(
    future: impl Future<Output = T> + 'static + Send,
    sched_type: SchedulerType,
) -> Option<T>
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

    rx.await.ok()
}
