//! Task yielding.

use crate::{task::perf::add_context_save_start, uptime};
use core::task::Poll;
use futures::Future;

#[must_use = "use `.await` to yield"]
pub struct Yield {
    yielded: bool,
}

impl Future for Yield {
    type Output = ();

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        if self.yielded {
            Poll::Ready(())
        } else {
            let y = self.get_mut();
            y.yielded = true;

            cx.waker().wake_by_ref();

            add_context_save_start(awkernel_lib::cpu::cpu_id(), uptime());
            Poll::Pending
        }
    }
}

impl Yield {
    pub(super) fn new() -> Self {
        Self { yielded: false }
    }
}
