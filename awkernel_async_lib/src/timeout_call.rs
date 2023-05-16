//! Timeout for async/await.

use super::{sleep_task::Sleep, Cancel};
use core::{pin::Pin, task::Poll, time::Duration};
use futures::{future::FusedFuture, Future, FutureExt};
use pin_project::pin_project;

#[must_use = "use `.await` to call"]
#[pin_project]
pub struct Timeout<F, T>
where
    F: Future<Output = T>,
{
    #[pin]
    future: F,
    sleep: Sleep,
    state: State,
}

enum State {
    Start,
    Await,
    Finished,
}

impl<F, T> Future for Timeout<F, T>
where
    F: Future<Output = T>,
{
    type Output = Option<T>;

    fn poll(
        self: Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        match self.state {
            State::Start => {
                let this = self.project();
                if let Poll::Ready(result) = this.future.poll(cx) {
                    return Poll::Ready(Some(result));
                }

                let _ = this.sleep.poll_unpin(cx);
                *this.state = State::Await;

                Poll::Pending
            }
            State::Await => {
                let this = self.project();
                if let Poll::Ready(result) = this.future.poll(cx) {
                    this.sleep.cancel_unpin();
                    *this.state = State::Finished;

                    Poll::Ready(Some(result))
                } else if this.sleep.is_terminated() {
                    *this.state = State::Finished;

                    Poll::Ready(None)
                } else {
                    Poll::Pending
                }
            }
            State::Finished => {
                unreachable!()
            }
        }
    }
}

impl<F, T> Timeout<F, T>
where
    F: Future<Output = T>,
{
    pub(super) fn new(duration: Duration, future: F) -> Self {
        Self {
            future,
            sleep: super::sleep_task::Sleep::new(duration.as_micros() as u64),
            state: State::Start,
        }
    }
}
