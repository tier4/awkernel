use alloc::{collections::VecDeque, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicBool, Ordering},
    task::{Poll, Waker},
};

pub struct AsyncLock<T> {
    data: UnsafeCell<T>,
    lock_var: AtomicBool,
    wakers: Arc<Mutex<VecDeque<Waker>>>,
}

pub struct AsyncLockGuard<'a, T> {
    lock: &'a AsyncLock<T>,
}

unsafe impl<T: Send> Send for AsyncLock<T> {}
unsafe impl<T: Send> Sync for AsyncLock<T> {}

impl<T> AsyncLock<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: UnsafeCell::new(data),
            lock_var: AtomicBool::new(false),
            wakers: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    pub fn lock(&self) -> AsyncLockFuture<'_, T> {
        AsyncLockFuture { lock: self }
    }
}

pub struct AsyncLockFuture<'a, T> {
    lock: &'a AsyncLock<T>,
}

impl<'a, T> core::future::Future for AsyncLockFuture<'a, T> {
    type Output = AsyncLockGuard<'a, T>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> Poll<Self::Output> {
        if self
            .lock
            .lock_var
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            Poll::Ready(AsyncLockGuard { lock: self.lock })
        } else {
            {
                let mut node = MCSNode::new();
                let mut wakers = self.lock.wakers.lock(&mut node);
                wakers.push_back(cx.waker().clone());
            }

            // To prevent starvation, check lock_var again
            if self.lock.lock_var.load(Ordering::Relaxed) {
                Poll::Pending
            } else {
                self.poll(cx)
            }
        }
    }
}

impl<T> Drop for AsyncLockGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.lock_var.store(false, Ordering::Release);

        let mut node = MCSNode::new();
        let mut wakers = self.lock.wakers.lock(&mut node);
        if let Some(waker) = wakers.pop_front() {
            waker.wake()
        }
    }
}

impl<T: Send> Deref for AsyncLockGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.lock.data.get() }
    }
}

impl<T: Send> DerefMut for AsyncLockGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<T: Send> AsMut<T> for AsyncLockGuard<'_, T> {
    fn as_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<T: Send> AsRef<T> for AsyncLockGuard<'_, T> {
    fn as_ref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::sync::Arc;

    #[test]
    fn test_simple_async_mutex() {
        let mutex = Arc::new(AsyncLock::new(0));
        let tasks = crate::mini_task::Tasks::new();

        for _ in 0..10000 {
            let mutex = mutex.clone();
            let task = async move {
                let mut guard = mutex.lock().await;
                let data = guard.as_mut();
                *data += 1;
            };

            tasks.spawn(task);
        }
        tasks.run();

        let mutex = mutex.clone();
        let task = async move {
            let guard = mutex.lock().await;
            let data = guard.as_ref();
            assert!(*data == 10000);
        };
        tasks.spawn(task);
        tasks.run();
    }
}
