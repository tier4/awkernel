use alloc::vec::Vec;

pub(super) struct RingQ<T> {
    queue: Vec<Option<T>>,
    size: usize,
    head: usize,
    tail: usize,
}

impl<T> RingQ<T> {
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
}
