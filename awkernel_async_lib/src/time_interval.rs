//! This module is based on Tokio's `interval` utility:
//! https://github.com/tokio-rs/tokio/blob/master/tokio/src/time/interval.rs
//!
//! The original source code is licensed under the MIT license:
//! https://github.com/tokio-rs/tokio/blob/master/LICENSE
//!
//! The original copyright notice is as follows:
//!
//! MIT License
//!
//! Copyright (c) Tokio Contributors
//!
//! Permission is hereby granted, free of charge, to any person obtaining a copy
//! of this software and associated documentation files (the "Software"), to deal
//! in the Software without restriction, including without limitation the rights
//! to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//! copies of the Software, and to permit persons to whom the Software is
//! furnished to do so, subject to the following conditions:
//!
//! The above copyright notice and this permission notice shall be included in all
//! copies or substantial portions of the Software.
//!
//! THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//! IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//! FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//! AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//! LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//! OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//! SOFTWARE.

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
    /// Ticks as fast as possible until caught up.
    ///
    /// This looks something like this:
    /// ```text
    /// Expected ticks: |     1     |     2     |     3     |     4     |     5     |     6     |
    /// Actual ticks:   | work -----|          delay          | work | work | work -| work -----|
    /// ```
    Burst,

    /// Ticks at the next available interval after the delay.
    ///
    /// This looks something like this:
    /// ```text
    /// Expected ticks: |     1     |     2     |     3     |     4     |     5     |     6     |
    /// Actual ticks:   | work -----|          delay          | work -----| work -----| work -----|
    /// ```
    Delay,

    /// Skips missed ticks and starts at the next tick.
    ///
    /// This looks something like this:
    /// ```text
    /// Expected ticks: |     1     |     2     |     3     |     4     |     5     |     6     |
    /// Actual ticks:   | work -----|          delay          | work ---| work -----| work -----|
    /// ```
    Skip,
}

impl Default for MissedTickBehavior {
    fn default() -> Self {
        Self::Burst
    }
}

/// Creates a new interval that ticks at the specified `period`.
/// The first tick completes immediately.
///
/// # Panics
/// Panics if `period` is zero.
///
/// # Example
///
/// ```ignore
/// extern crate alloc;
///
/// use crate::time_interval::interval;
/// use core::time::Duration;
///
/// let mut interval = interval(Duration::from_secs(1));
/// let mut ticks = 0;
/// while ticks < 5 {
///     let tick_time = interval.tick().await;
///     println!("Tick at: {:?}", tick_time);
///     ticks += 1;
/// }
/// ```
///
pub fn interval(period: Duration) -> Interval {
    assert!(!period.is_zero(), "`period` must be non-zero.");
    interval_at(Time::now(), period)
}

pub fn interval_at(start: Time, period: Duration) -> Interval {
    assert!(!period.is_zero(), "`period` must be non-zero.");
    Interval {
        delay: None,
        next_tick_target: start,
        period,
        period_nanos: period.as_nanos(),
        missed_tick_behavior: MissedTickBehavior::default(),
    }
}

pub struct Interval {
    next_tick_target: Time,
    delay: Option<Pin<Box<Sleep>>>,
    period: Duration,
    period_nanos: u128,
    missed_tick_behavior: MissedTickBehavior,
}

impl Interval {
    pub async fn tick(&mut self) -> Time {
        self.next().await.unwrap()
    }
}

impl Stream for Interval {
    type Item = Time;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        if self.delay.is_none() {
            let now = Time::now();
            let wait_duration = self.next_tick_target.saturating_duration_since(now);
            let sleep_future = Box::pin(Sleep::new(wait_duration));
            self.delay = Some(sleep_future);
        }

        let tick_time = self.next_tick_target;
        let period = self.period;

        let sleep_future = self.delay.as_mut().unwrap();
        match sleep_future.as_mut().poll(cx) {
            Poll::Pending => Poll::Pending,
            Poll::Ready(_) => {
                let now = Time::now();
                // If a tick is missed, determine the target time for the next tick.
                let next_target = if now > tick_time {
                    match self.missed_tick_behavior {
                        MissedTickBehavior::Burst => tick_time + period,
                        MissedTickBehavior::Delay => now + period,
                        MissedTickBehavior::Skip => {
                            let ticks_missed = (now.saturating_duration_since(tick_time).as_nanos()
                                / self.period_nanos)
                                as u32;
                            tick_time + period * (ticks_missed + 1)
                        }
                    }
                } else {
                    tick_time + period
                };
                self.next_tick_target = next_target;
                self.delay = None;

                Poll::Ready(Some(tick_time))
            }
        }
    }
}
