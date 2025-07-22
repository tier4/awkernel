use alloc::boxed::Box;
use awkernel_lib::time::Time;
use core::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
    time::Duration,
};
use futures::Stream;

use crate::sleep_task::Sleep;

#[must_use = "streams do nothing unless polled"]
pub struct Interval {
    next_tick_target: Time,
    period: Duration,
    sleep: Option<Pin<Box<Sleep>>>,
}

impl Interval {
    pub fn new(period: Duration) -> Self {
        let now = Time::now();
        Interval {
            next_tick_target: now,
            period,
            sleep: None,
        }
    }
}

impl Stream for Interval {
    type Item = Time;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        if self.sleep.is_none() {
            let now = Time::now();
            let wait_duration = self.next_tick_target.saturating_duration_since(now);
            let sleep_future = Box::pin(Sleep::new(wait_duration));
            self.sleep = Some(sleep_future);
        }

        let tick_time = self.next_tick_target;
        let period = self.period;

        let sleep_future = self.sleep.as_mut().unwrap();
        match sleep_future.as_mut().poll(cx) {
            Poll::Pending => Poll::Pending,
            Poll::Ready(_) => {
                self.next_tick_target = tick_time + period;
                self.sleep = None;

                Poll::Ready(Some(tick_time))
            }
        }
    }
}
