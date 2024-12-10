use alloc::collections::VecDeque;

pub struct PriorityQueue<T> {
    queue: [VecDeque<T>; 32],
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
        let queue = &mut self.queue[priority as usize];
        queue.push_back(val);
        self.has_entry |= 1 << priority;
    }

    pub fn pop(&mut self) -> Option<T> {
        let next_priority = self.has_entry.trailing_zeros();
        if next_priority == 32 {
            return None;
        }

        let queue = &mut self.queue[next_priority as usize];
        let next = queue.pop_front();
        assert!(next.is_some());
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
    fn test_prioriry_queue() {
        let mut q = PriorityQueue::new();

        // Queue should be empty
        assert_eq!(q.pop(), None);

        for id in 0..10 {
            q.push(0, id);
        }

        // Data with the same priority should be popped in a FIFO order
        for expected in 0..10 {
            let actual = q.pop().unwrap();
            assert_eq!(actual, expected);
        }

        for id in 0..10 {
            q.push(10 - id, id);
        }

        // Data with different priorities are popped from the highest priority first
        for expected in (0..10).rev() {
            let actual = q.pop().unwrap();
            assert_eq!(actual, expected);
        }

        // Queue should be empty
        assert_eq!(q.pop(), None);
    }
}

// TODO: Verification
