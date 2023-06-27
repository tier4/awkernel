//! Simple ring queue implementation.

use alloc::vec::Vec;

/// Ring queue.
pub struct RingQ<T> {
    queue: Vec<Option<T>>,
    size: usize,
    head: usize,
    tail: usize,
}

impl<T> RingQ<T> {
    /// Create a ring queue.
    pub fn new(queue_size: usize) -> Self {
        let mut queue = Vec::new();
        queue.resize_with(queue_size, || None);

        Self {
            queue,
            size: 0,
            head: 0,
            tail: 0,
        }
    }

    pub fn is_full(&self) -> bool {
        self.size >= self.queue.len()
    }

    /// Push `data` to the queue.
    pub fn push(&mut self, data: T) -> Result<(), T> {
        if self.queue.len() == self.size {
            return Err(data);
        }

        self.queue[self.tail] = Some(data);
        self.tail += 1;
        if self.tail == self.queue.len() {
            self.tail = 0;
        }

        self.size += 1;

        Ok(())
    }

    /// Pop data from the queue.
    pub fn pop(&mut self) -> Option<T> {
        if self.size == 0 {
            None
        } else {
            let result = self.queue[self.head].take();

            self.head += 1;
            if self.head == self.queue.len() {
                self.head = 0;
            }

            self.size -= 1;

            result
        }
    }

    /// Get the immutable reference of the head.
    pub fn head(&self) -> &Option<T> {
        &self.queue[self.head]
    }

    /// Get a iterator.
    pub fn iter(&self) -> IterRingQ<T> {
        IterRingQ {
            ringq: self,
            pos: self.head,
        }
    }
}

/// Iterator of `RingQ`.
pub struct IterRingQ<'a, T> {
    ringq: &'a RingQ<T>,
    pos: usize,
}

impl<'a, T> Iterator for IterRingQ<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.ringq.tail == self.pos {
            None
        } else if let Some(result) = &self.ringq.queue[self.pos] {
            self.pos += 1;
            Some(result)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ringq() {
        let mut q = RingQ::new(10);

        for i in 0..10 {
            q.push(i).unwrap();
        }

        for i in 0..10 {
            let data = q.pop().unwrap();
            assert_eq!(i, data);
        }

        for i in 0..10 {
            q.push(i).unwrap();
        }

        for i in 0..10 {
            let data = q.pop().unwrap();
            assert_eq!(i, data);
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

        for i in num1..num1+num2 {
            q.push(i);
        }

        while let Some(data) = q.pop() {
            assert!(expected == data);
            expected += 1;
        }
    }
}