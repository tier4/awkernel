//! Simple ring queue implementation.

use alloc::vec::Vec;

/// Ring queue.
pub struct RingQ<T> {
    queue: Vec<Option<T>>,
    len: usize,
    head: usize,
    tail: usize,
}

impl<T> RingQ<T> {
    /// Create a ring queue.
    pub fn new(queue_len: usize) -> Self {
        let mut queue = Vec::new();
        queue.resize_with(queue_len, || None);

        Self {
            queue,
            len: 0,
            head: 0,
            tail: 0,
        }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline(always)]
    pub fn queue_size(&self) -> usize {
        self.queue.len()
    }

    #[inline(always)]
    pub fn is_full(&self) -> bool {
        self.len >= self.queue.len()
    }

    /// Push `data` to the queue.
    pub fn push(&mut self, data: T) -> Result<(), T> {
        if self.queue.len() == self.len {
            return Err(data);
        }

        self.queue[self.tail] = Some(data);
        self.tail += 1;
        if self.tail == self.queue.len() {
            self.tail = 0;
        }

        self.len += 1;

        Ok(())
    }

    /// Pop data from the queue.
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            let result = self.queue[self.head].take();

            self.head += 1;
            if self.head == self.queue.len() {
                self.head = 0;
            }

            self.len -= 1;

            result
        }
    }

    /// Get the immutable reference of the head.
    #[inline(always)]
    pub fn head(&self) -> &Option<T> {
        &self.queue[self.head]
    }

    /// Get a iterator.
    #[inline(always)]
    pub fn iter(&self) -> IterRingQ<'_, T> {
        IterRingQ {
            ringq: self,
            pos: self.head,
            len: self.len,
        }
    }
}

/// Iterator of `RingQ`.
pub struct IterRingQ<'a, T> {
    ringq: &'a RingQ<T>,
    len: usize,
    pos: usize,
}

impl<'a, T> Iterator for IterRingQ<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            match &self.ringq.queue[self.pos] {
                Some(result) => {
                    self.pos += 1;
                    if self.pos == self.ringq.queue.len() {
                        self.pos = 0;
                    }
                    self.len -= 1;
                    Some(result)
                }
                None => unreachable!(), // This should never happen
            }
        }
    }
}

impl<'a, T> ExactSizeIterator for IterRingQ<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ringq() {
        let mut q = RingQ::new(10);

        for _ in 0..10 {
            for i in 0..10 {
                assert!(q.push(i).is_ok());
                assert_eq!(q.len(), i + 1);
                assert_eq!(q.head, 0);
                assert_eq!(q.tail, (i + 1) % 10);
            }
            assert_eq!(q.head, 0);
            assert_eq!(q.tail, 0);
            assert!(q.is_full());
            assert!(q.push(10).is_err());

            for i in 0..10 {
                let data = q.pop().unwrap();
                assert_eq!(i, data);
                assert_eq!(q.head, (i + 1) % 10);
                assert_eq!(q.tail, 0);
            }
            assert_eq!(q.head, 0);
            assert_eq!(q.tail, 0);
            assert!(q.is_empty());
            assert!(q.pop().is_none());
        }
    }

    #[test]
    fn test_ringq_iter() {
        let mut q = RingQ::new(10);

        // We will test the iterator starting from all different positions of the head.
        for i in 0..=10 {
            // Push-pop one element to move the head and tail to the next position.
            assert!(q.push(0).is_ok());
            assert!(q.pop().is_some());

            assert_eq!(q.head, (i + 1) % 10);
            assert_eq!(q.tail, (i + 1) % 10);
            assert!(q.is_empty());

            // Fill the queue
            for j in 0..10 {
                assert!(q.push(j).is_ok());
            }
            assert_eq!(q.head, (i + 1) % 10);
            assert_eq!(q.tail, (i + 1) % 10);
            assert!(q.is_full());

            // Test the iterator.
            let mut iter = q.iter();
            assert_eq!(iter.len(), 10);
            for j in 0..10 {
                let data = iter.next();
                assert_eq!(data, Some(&j));
            }

            // Empty the queue for the next iteration
            while let Some(_) = q.pop() {}
        }
    }
}

#[cfg(kani)]
mod verification {
    use super::*;

    #[kani::proof]
    #[kani::unwind(11)]
    pub fn verify_ringq() {
        let q_size = 10;
        let mut q = RingQ::new(q_size);

        let num1: usize = kani::any();
        kani::assume(num1 <= q_size);

        let num2: usize = kani::any();
        kani::assume(num2 <= q_size && num1 + num2 > q_size);

        let num3: usize = kani::any();
        kani::assume(num3 < num1);
        kani::assume(num1 - num3 + num2 <= q_size);

        for i in 0..num1 {
            q.push(i);
        }

        let mut expected = 0;
        for _ in 0..num3 {
            let data = q.pop().unwrap();
            assert!(expected == data);
            expected += 1;
        }

        for i in num1..num1 + num2 {
            q.push(i);
        }

        while let Some(data) = q.pop() {
            assert!(expected == data);
            expected += 1;
        }
    }
}
