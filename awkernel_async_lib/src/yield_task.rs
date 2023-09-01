//! Task yielding.

use awkernel_lib::{delay::uptime, sync::mutex::MCSNode, POLL_TIMESTAMPS};
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
        let mut node = MCSNode::new();
        let mut poll_timestamps = POLL_TIMESTAMPS[awkernel_lib::cpu::cpu_id()].lock(&mut node);
        poll_timestamps.1 = uptime(); // End poll() restore_time

        if self.yielded {
            Poll::Ready(())
        } else {
            let y = self.get_mut();
            y.yielded = true;

            cx.waker().wake_by_ref();

            poll_timestamps.0 = uptime(); // Start poll() save_time
            Poll::Pending
        }
    }
}

impl Yield {
    pub(super) fn new() -> Self {
        Self { yielded: false }
    }
}
