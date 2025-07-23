use crate::sleep_task::Sleep;
use alloc::boxed::Box;
use awkernel_lib::time::Time;
use core::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
    time::Duration,
};
use futures::Stream;
use futures::StreamExt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(unused)]
pub enum MissedTickBehavior {
    Burst,
    Delay,
    Skip,
}

impl Default for MissedTickBehavior {
    fn default() -> Self {
        Self::Burst
    }
}

pub fn interval(period: Duration) -> Interval {
    assert!(!period.is_zero(), "`period` must be non-zero.");
    interval_at(Time::now(), period)
}

pub fn interval_at(start: Time, period: Duration) -> Interval {
    assert!(!period.is_zero(), "`period` must be non-zero.");
    Interval {
        next_tick_target: start,
        period,
        sleep: None,
        missed_tick_behavior: MissedTickBehavior::default(),
    }
}

pub struct Interval {
    next_tick_target: Time,
    period: Duration,
    sleep: Option<Pin<Box<Sleep>>>,
    missed_tick_behavior: MissedTickBehavior,
}

impl Interval {
    pub fn get_next_tick_target(&self) -> Time {
        self.next_tick_target
    }

    pub async fn tick(&mut self) -> Time {
        self.next().await.unwrap()
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
                let now = Time::now();
                let next_target = if now > tick_time {
                    match self.missed_tick_behavior {
                        MissedTickBehavior::Burst => tick_time + period,
                        MissedTickBehavior::Delay => now + period,
                        MissedTickBehavior::Skip => {
                            let ticks_missed = (now.saturating_duration_since(tick_time).as_nanos()
                                / period.as_nanos())
                                as u32;
                            tick_time + period * (ticks_missed + 1)
                        }
                    }
                } else {
                    tick_time + period
                };
                self.next_tick_target = next_target;
                self.sleep = None;

                Poll::Ready(Some(tick_time))
            }
        }
    }
}
