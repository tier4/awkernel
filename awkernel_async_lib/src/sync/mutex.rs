use alloc::collections::VecDeque;
use core::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicBool, Ordering},
    task::{Poll, Waker},
};

pub struct AsyncLock<T> {
    data: UnsafeCell<T>,
    lock_var: AtomicBool,
    wakers: UnsafeCell<VecDeque<Waker>>,
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
            wakers: UnsafeCell::new(VecDeque::new()),
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
            unsafe {
                (*self.lock.wakers.get()).push_back(cx.waker().clone());
            }

            Poll::Pending

            // [WIP] To prevent starvation, check mutex again
            // if self.lock.lock_var.load(Ordering::Relaxed) {
            //     Poll::Pending
            // } else {
            //     self.poll(cx)
            // }
        }
    }
}

impl<T> Drop for AsyncLockGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.lock_var.store(false, Ordering::Release);

        unsafe {
            let wakers = &mut *self.lock.wakers.get();
            if let Some(waker) = wakers.pop_front() {
                waker.wake()
            }
        }
    }
}

impl<T> Deref for AsyncLockGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.lock.data.get() }
    }
}

impl<T> DerefMut for AsyncLockGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.lock.data.get() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::sync::Arc;
    use awkernel_lib::delay::wait_millisec;

    #[test]
    fn test_simple_async_mutex() {
        let mutex = Arc::new(AsyncLock::new(0));
        let tasks = crate::mini_task::Tasks::new();

        for _ in 0..10000 {
            let mutex = mutex.clone();
            let task = async move {
                let mut guard = mutex.lock().await;
                let data = guard.deref_mut();
                *data += 1;
            };

            tasks.spawn(task);
        }
        tasks.run();

        let mutex = mutex.clone();
        let task = async move {
            let guard = mutex.lock().await;
            let data = guard.deref();
            assert!(*data == 10000);
        };

        tasks.spawn(task);
        tasks.run();
    }

    #[test]
    fn test_multiple_wakers() {
        let mutex = Arc::new(AsyncLock::new(0));
        let tasks = crate::mini_task::Tasks::new();

        // Generate a heavy task so that subsequent tasks will be blocked
        {
            let mutex = mutex.clone();
            let task = async move {
                let mut guard = mutex.lock().await;
                let data = guard.deref_mut();
                wait_millisec(100);
                *data = 1;
            };
            tasks.spawn(task);
            tasks.run();
        }

        for _ in 0..100 {
            let mutex = mutex.clone();
            let task = async move {
                let mut guard = mutex.lock().await;
                let data = guard.deref_mut();
                *data += 1;
            };
            tasks.spawn(task);
        }
        tasks.run();

        let mutex = mutex.clone();
        let task = async move {
            let guard = mutex.lock().await;
            let data = guard.deref();
            assert!(*data == 101);
        };

        tasks.spawn(task);
        tasks.run();
    }
}
