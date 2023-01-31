use core::{
    sync::atomic::{AtomicBool, Ordering},
    task::{Context, Poll},
};

use alloc::{collections::VecDeque, sync::Arc};
use futures::{
    future::BoxFuture,
    task::{waker_ref, ArcWake},
    Future, FutureExt,
};
use synctools::mcs::{MCSLock, MCSNode};

pub struct Task {
    future: MCSLock<BoxFuture<'static, ()>>,
    queue: Arc<MCSLock<VecDeque<Arc<Task>>>>,
    terminated: AtomicBool,
}

unsafe impl Sync for Task {}
unsafe impl Send for Task {}

impl ArcWake for Task {
    fn wake_by_ref(arc_self: &Arc<Self>) {
        let cloned = arc_self.clone();
        cloned.wake();
    }

    fn wake(self: Arc<Self>) {
        let mut node = MCSNode::new();
        let mut queue = self.queue.lock(&mut node);
        queue.push_back(self.clone());
    }
}

pub struct Tasks {
    queue: Arc<MCSLock<VecDeque<Arc<Task>>>>,
}

impl Tasks {
    pub fn new() -> Self {
        Self {
            queue: Arc::new(MCSLock::new(VecDeque::new())),
        }
    }

    pub fn run(&self) {
        loop {
            let Some(head) = ({
                let mut node = MCSNode::new();
                let mut queue = self.queue.lock(&mut node);
                queue.pop_front()
            }) else { return };

            if head.terminated.load(Ordering::Relaxed) {
                continue;
            }

            let w = waker_ref(&head);
            let mut cx = Context::from_waker(&w);

            let mut node = MCSNode::new();
            let mut future = head.future.lock(&mut node);

            match future.as_mut().poll(&mut cx) {
                Poll::Pending => {
                    future.unlock();

                    let mut node = MCSNode::new();
                    let mut queue = self.queue.lock(&mut node);
                    queue.push_back(head);
                }
                Poll::Ready(_) => {
                    head.terminated.store(true, Ordering::Relaxed);
                }
            }
        }
    }

    pub fn spawn(&self, future: impl Future<Output = ()> + 'static + Send) {
        let q = self.queue.clone();

        let mut node = MCSNode::new();
        let mut queue = self.queue.lock(&mut node);

        let task = Task {
            future: MCSLock::new(future.boxed()),
            queue: q,
            terminated: AtomicBool::new(false),
        };

        queue.push_back(Arc::new(task));
    }
}
