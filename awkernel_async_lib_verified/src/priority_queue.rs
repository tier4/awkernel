use alloc::collections::VecDeque;

pub struct PriorityQueue<T> {
    queue: [Option<VecDeque<T>>; 32],
    has_entry: u32,
}

impl<T> PriorityQueue<T> {
    pub fn new() -> Self {
        Self {
            queue: Default::default(),
            has_entry: 0,
        }
    }

    pub fn push(&mut self, priority: u32, val: T) {
        assert!(priority < 32);
        if let Some(queue) = self.queue[priority as usize].as_mut() {
            queue.push_back(val);
        } else {
            let queue = VecDeque::from([val]);
            self.queue[priority as usize] = Some(queue);
        }
        self.has_entry |= 1 << priority;
    }

    pub fn pop(&mut self) -> Option<T> {
        let next_priority = self.has_entry.trailing_zeros();
        if next_priority == 32 {
            return None;
        }

        let queue = self.queue[next_priority as usize].as_mut().unwrap();
        let next = queue.pop_front();

        if queue.is_empty() {
            self.has_entry &= !(1 << next_priority);
        }

        next
    }
}

impl<T> Default for PriorityQueue<T> {
    fn default() -> Self {
        Self::new()
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
        assert_eq!(q.pop(), None);
        q.push(0, S(0));
        q.push(0, S(1));
        q.push(0, S(2));
        q.push(0, S(3));

        assert_eq!(q.pop().unwrap(), S(0));
        assert_eq!(q.pop().unwrap(), S(1));
        assert_eq!(q.pop().unwrap(), S(2));
        assert_eq!(q.pop().unwrap(), S(3));
        assert_eq!(q.pop(), None);
    }
}

#[cfg(kani)]
mod verification {
    use super::*;

    #[kani::proof]
    #[kani::unwind(11)]
    pub fn verify_priority_queue_fifo() {
        let mut q = PriorityQueue::new();

        assert!(q.pop() == None);

        let priority = 0;
        let len = kani::any();
        kani::assume(len <= 10);

        for i in 0..len {
            q.push(priority, i);
        }

        for expected in 0..len {
            let actual = q.pop().unwrap();
            assert!(actual == expected);
        }

        assert!(q.pop() == None);
    }
}
