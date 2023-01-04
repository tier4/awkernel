use crate::scheduler;
use alloc::{boxed::Box, sync::Arc};
use core::{task::Poll, time::Duration};
use futures::Future;
use synctools::mcs::{MCSLock, MCSNode};

use super::Cancel;

#[must_use = "use `.await` to sleep"]
pub struct Sleep {
    state: Arc<MCSLock<State>>,
    dur: u64,
}

#[derive(Debug)]
pub enum State {
    Ready,
    Wait,
    Canceled,
    Finished,
}

impl Future for Sleep {
    type Output = State;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let mut node = MCSNode::new();
        let mut guard = self.state.lock(&mut node);

        match &*guard {
            State::Wait => Poll::Pending,
            State::Canceled => Poll::Ready(State::Canceled),
            State::Finished => Poll::Ready(State::Finished),
            State::Ready => {
                let state = self.state.clone();
                let waker = cx.waker().clone();

                *guard = State::Wait;

                scheduler::sleep_task(
                    Box::new(move || {
                        let mut node = MCSNode::new();
                        let mut guard = state.lock(&mut node);
                        if let State::Wait = &*guard {
                            *guard = State::Finished;
                        }

                        waker.wake();
                    }),
                    self.dur,
                );

                Poll::Pending
            }
        }
    }
}

impl Cancel for Sleep {
    fn cancel(self: core::pin::Pin<&mut Self>) {
        let mut node = MCSNode::new();
        let mut guard = self.state.lock(&mut node);

        match &*guard {
            State::Ready | State::Wait => {
                *guard = State::Canceled;
            }
            _ => (),
        }
    }
}

impl Sleep {
    fn new(dur: u64) -> Self {
        let state = Arc::new(MCSLock::new(State::Ready));
        Self { state, dur }
    }
}

impl Drop for Sleep {
    fn drop(&mut self) {
        let mut node = MCSNode::new();
        let mut guard = self.state.lock(&mut node);
        if let State::Wait = &*guard {
            *guard = State::Canceled;
        }
    }
}

pub fn sleep(duration: Duration) -> Sleep {
    Sleep::new(duration.as_micros() as u64)
}
