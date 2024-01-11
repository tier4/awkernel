//use alloc::{collections::VecDeque, sync::Arc};
use core::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicBool, Ordering},
    task::Poll,
};
use futures::Future;

pub struct AsyncLock<T> {
    lock_var: AtomicBool,
    data: UnsafeCell<T>,
    // TODO
    // wakers: VecDeque<Waker>,
}

unsafe impl<T: Send> Sync for AsyncLock<T> {}
unsafe impl<T: Send> Send for AsyncLock<T> {}

impl<T> AsyncLock<T> {
    pub const fn new(data: T) -> Self {
        AsyncLock {
            lock_var: AtomicBool::new(false),
            data: UnsafeCell::new(data),
            // TODO
            // wakers: Default::default(),
        }
    }

    pub async fn lock(&self) -> AsyncLockGuard<T> {
        let async_lock_guard = AsyncLockGuard { async_lock: self };

        if self
            .lock_var
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            // TODO: solve priority inversion
            async_lock_guard
        } else {
            // TODO: solve priority inversion

            // TODO: if locked by another thread, preserve the waker to be awaken later
            // let waker = ...
            // self.wakers.push_back(waker);

            async_lock_guard.await
        }
    }
}

pub struct AsyncLockGuard<'a, T> {
    async_lock: &'a AsyncLock<T>,
}

impl<'a, T> Future for AsyncLockGuard<'a, T> {
    type Output = Self;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        _cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        loop {
            if self
                .async_lock
                .lock_var
                .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                let async_lock_guard = AsyncLockGuard {
                    async_lock: self.async_lock,
                };
                return Poll::Ready(async_lock_guard);
            }
        }
    }
}

impl<'a, T> Drop for AsyncLockGuard<'a, T> {
    fn drop(&mut self) {
        self.async_lock.lock_var.store(false, Ordering::Release);

        // TODO: if wakers queue is not empty, then pop and wake it
        // if !self.async_lock.wakers.is_empty() {
        //     let Some(waker) = self.async_lock.wakers.pop_front();
        //     waker.wake()
        // }
    }
}

impl<'a, T: Send> Deref for AsyncLockGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.async_lock.data.get() }
    }
}

impl<'a, T: Send> DerefMut for AsyncLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.async_lock.data.get() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::sync::Arc;

    #[test]
    fn test_async_mutex() {
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
}
