//! Sleep a task forever.

use core::task::Poll;
use futures::Future;

pub struct Never;

impl Future for Never {
    type Output = ();
    fn poll(
        self: core::pin::Pin<&mut Self>,
        _cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        Poll::Pending
    }
}
