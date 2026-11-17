use alloc::collections::VecDeque;

pub const HIGHEST_PRIORITY: u8 = 31;

pub struct PriorityQueue<T> {
    queue: [VecDeque<T>; HIGHEST_PRIORITY as usize + 1],
    has_entry: u32,
}

impl<T> PriorityQueue<T> {
    pub fn new() -> Self {
        Self {
            queue: Default::default(),
            has_entry: 0,
        }
    }

    /// Push the value with the specified priority
    /// Note: the priority is set to min(priority, HIGHEST_PRIORITY)
    #[inline(always)]
    pub fn push(&mut self, priority: u8, val: T) {
        let priority = priority.min(HIGHEST_PRIORITY);
        let queue = &mut self.queue[priority as usize];
        queue.push_back(val);
        self.has_entry |= 1 << priority;
    }

    /// Pop the value with the highest priority
    #[inline(always)]
    pub fn pop(&mut self) -> Option<T> {
        if self.has_entry == 0 {
            return None;
        }
        let next_priority = (u32::BITS - 1) - self.has_entry.leading_zeros();

        let queue = &mut self.queue[next_priority as usize];
        let next = queue.pop_front();
        assert!(next.is_some());
        if queue.is_empty() {
            self.has_entry &= !(1 << next_priority);
        }

        next
    }

    /// Return a reference to the value that `pop` would return, without removing it
    #[inline(always)]
    pub fn peek(&self) -> Option<&T> {
        if self.has_entry == 0 {
            return None;
        }
        let next_priority = (u32::BITS - 1) - self.has_entry.leading_zeros();

        self.queue[next_priority as usize].front()
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
    fn test_priority_queue() {
        let mut q = PriorityQueue::new();

        // Queue should be empty
        assert_eq!(q.pop(), None);

        // Data with the same priority should be popped in a FIFO order
        for id in 0..10 {
            q.push(0, id);
        }

        for expected in 0..10 {
            let actual = q.pop().unwrap();
            assert_eq!(actual, expected);
        }

        // Data with different priorities are popped from the highest priority first
        for id in 0..10 {
            q.push(id, id);
        }

        for expected in (0..10).rev() {
            let actual = q.pop().unwrap();
            assert_eq!(actual, expected);
        }

        //  The priority is set to min(priority, HIGHEST_PRIORITY)
        for id in (0..10).step_by(2) {
            q.push(HIGHEST_PRIORITY, id);
            q.push(HIGHEST_PRIORITY + 1, id + 1);
        }

        for expected in 0..10 {
            let actual = q.pop().unwrap();
            assert_eq!(actual, expected);
        }

        // Queue should be empty
        assert_eq!(q.pop(), None);
    }

    #[test]
    fn test_priority_queue_peek() {
        let mut q = PriorityQueue::new();

        // Nothing to peek in an empty queue
        assert_eq!(q.peek(), None);

        // `peek` returns the head of the FIFO order and does not remove it
        for id in 0..10 {
            q.push(0, id);
        }

        for expected in 0..10 {
            assert_eq!(q.peek(), Some(&expected));
            assert_eq!(q.peek(), Some(&expected));
            assert_eq!(q.pop(), Some(expected));
        }

        assert_eq!(q.peek(), None);

        // `peek` returns the value with the highest priority
        q.push(1, 10);
        assert_eq!(q.peek(), Some(&10));
        q.push(3, 30);
        assert_eq!(q.peek(), Some(&30));
        q.push(2, 20);
        assert_eq!(q.peek(), Some(&30));
        q.push(3, 31);
        assert_eq!(q.peek(), Some(&30));

        // `peek` always agrees with the following `pop`
        while let Some(expected) = q.peek().copied() {
            assert_eq!(q.pop(), Some(expected));
        }

        assert_eq!(q.pop(), None);
    }
}

// TODO: Verification
