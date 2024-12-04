use crate::sync::{mcs::MCSNode, mutex::Mutex};

pub const EVAL_COUNT: usize = 1000;

pub struct TimeEval {
    inner: Mutex<TimeEvalInner>,
}

struct TimeEvalInner {
    time: u128,
    count: usize,
}

impl TimeEval {
    pub const fn new() -> Self {
        Self {
            inner: Mutex::new(TimeEvalInner { time: 0, count: 0 }),
        }
    }

    pub fn add(&self, time: u128) -> usize {
        let mut node = MCSNode::new();
        let mut inner = self.inner.lock(&mut node);
        inner.time += time;
        inner.count += 1;

        inner.count
    }

    pub fn average(&self) -> f64 {
        let mut node = MCSNode::new();
        let inner = self.inner.lock(&mut node);
        if inner.count == 0 {
            0.0
        } else {
            inner.time as f64 / inner.count as f64
        }
    }

    pub fn reset(&self) {
        let mut node = MCSNode::new();
        let mut inner = self.inner.lock(&mut node);
        inner.time = 0;
        inner.count = 0;
    }
}
