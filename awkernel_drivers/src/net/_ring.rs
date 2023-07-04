use super::mbuf::MBuf;
use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mcs::{MCSLock, MCSNode};

pub trait Ring {
    fn push(&self, mbuf: MBuf);
    fn pop(&self) -> Option<MBuf>;
}

pub struct RecvRing {
    queue: Arc<MCSLock<VecDeque<MBuf>>>,
}
pub struct SendRing {
    queue: Arc<MCSLock<VecDeque<MBuf>>>,
}

impl Ring for RecvRing {
    fn pop(&self) -> Option<MBuf> {
        let mut node = MCSNode::new();
        let mut guard = self.queue.lock(&mut node);
        guard.pop_front()
    }
    fn push(&self, mbuf: MBuf) {
        let mut node = MCSNode::new();
        let mut guard = self.queue.lock(&mut node);
        guard.push_back(mbuf);
    }
}

impl Ring for SendRing {
    fn pop(&self) -> Option<MBuf> {
        let mut node = MCSNode::new();
        let mut guard = self.queue.lock(&mut node);
        guard.pop_front()
    }
    fn push(&self, mbuf: MBuf) {
        let mut node = MCSNode::new();
        let mut guard = self.queue.lock(&mut node);
        guard.push_back(mbuf);
    }
}
