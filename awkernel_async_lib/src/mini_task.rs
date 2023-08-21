//! A task runner used by test.

use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::task::Context;
use futures::{
    future::{BoxFuture, Fuse, FusedFuture},
    task::{waker_ref, ArcWake},
    Future, FutureExt,
};

pub struct Task {
    future: Mutex<Fuse<BoxFuture<'static, ()>>>,
    queue: Arc<Mutex<VecDeque<Arc<Task>>>>,
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
    queue: Arc<Mutex<VecDeque<Arc<Task>>>>,
}

impl Tasks {
    pub fn new() -> Self {
        Self {
            queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    pub fn run(&self) {
        loop {
            let Some(head) = ({
                let mut node = MCSNode::new();
                let mut queue = self.queue.lock(&mut node);
                queue.pop_front()
            }) else {
                return;
            };

            let w = waker_ref(&head);
            let mut cx = Context::from_waker(&w);

            let mut node = MCSNode::new();
            let mut future = head.future.lock(&mut node);

            if future.is_terminated() {
                continue;
            }

            let _ = future.poll_unpin(&mut cx);
        }
    }

    pub fn spawn(&self, future: impl Future<Output = ()> + 'static + Send) {
        let q = self.queue.clone();

        let mut node = MCSNode::new();
        let mut queue = self.queue.lock(&mut node);

        let task = Task {
            future: Mutex::new(future.boxed().fuse()),
            queue: q,
        };

        queue.push_back(Arc::new(task));
    }
}
