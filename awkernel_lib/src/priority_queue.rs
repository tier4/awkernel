use alloc::collections::{BTreeMap, VecDeque};

pub struct PriorityQueue<T> {
    queue: BTreeMap<usize, VecDeque<T>>,
}

impl<T> PriorityQueue<T> {
    pub fn new() -> Self {
        Self {
            queue: BTreeMap::new(),
        }
    }

    pub fn push(&mut self, priority: usize, val: T) {
        if let Some(queue) = self.queue.get_mut(&priority) {
            queue.push_back(val);
        } else {
            self.queue.insert(priority, VecDeque::from([val]));
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        if let Some((priority, mut queue)) = self.queue.pop_first() {
            assert!(!queue.is_empty());
            let next_val = queue.pop_front();
            if !queue.is_empty() {
                self.queue.insert(priority, queue);
            }
            next_val
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    /// Unlike alloc::collections::BinaryHeap, PriorityQueue guarantees that data with the same priority will be retrieved in FIFO order.
    fn test_prioriry_queue_fifo() {
        #[derive(Debug, PartialEq)]
        struct S(usize);

        let mut q = PriorityQueue::new();
        q.push(0, S(0));
        q.push(0, S(1));
        q.push(0, S(2));
        q.push(0, S(3));

        assert_eq!(q.pop().unwrap(), S(0));
        assert_eq!(q.pop().unwrap(), S(1));
        assert_eq!(q.pop().unwrap(), S(2));
        assert_eq!(q.pop().unwrap(), S(3));
    }
}
