use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

#[cfg(not(loom))]
use core::{
    cell::UnsafeCell,
    hint,
    sync::atomic::{AtomicUsize, Ordering},
};

#[cfg(loom)]
use loom::{
    cell::UnsafeCell,
    hint,
    sync::atomic::{AtomicUsize, Ordering},
};

pub struct RwLock<T: Send> {
    state: AtomicUsize,
    writer_wake_counter: AtomicUsize,
    data: UnsafeCell<T>,
}

impl<T: Send> RwLock<T> {
    #[cfg(not(loom))]
    pub const fn new(v: T) -> RwLock<T> {
        RwLock {
            state: AtomicUsize::new(0),
            writer_wake_counter: AtomicUsize::new(0),
            data: UnsafeCell::new(v),
        }
    }

    #[cfg(loom)]
    pub fn new(v: T) -> RwLock<T> {
        RwLock {
            state: AtomicUsize::new(0),
            writer_wake_counter: AtomicUsize::new(0),
            data: UnsafeCell::new(v),
        }
    }

    /// acquire reader lock
    #[inline(always)]
    pub fn read(&self) -> RwLockReadGuard<T> {
        let _interrupt_guard = crate::interrupt_guard::InterruptGuard::new();

        let mut s = self.state.load(Ordering::Relaxed);
        loop {
            if s & 1 == 0 {
                match self.state.compare_exchange_weak(
                    s,
                    s + 2,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => {
                        return RwLockReadGuard {
                            rwlock: self,
                            _interrupt_guard,
                            _phantom: Default::default(),
                        };
                    }
                    Err(e) => s = e,
                }
            }

            if s & 1 == 1 {
                while self.state.load(Ordering::Relaxed) == s {
                    hint::spin_loop();

                    #[cfg(loom)]
                    loom::thread::yield_now();
                }
                s = self.state.load(Ordering::Relaxed);
            }

            #[cfg(loom)]
            loom::thread::yield_now();
        }
    }

    /// acquire writer lock
    #[inline(always)]
    pub fn write(&self) -> RwLockWriteGuard<T> {
        let _interrupt_guard = crate::interrupt_guard::InterruptGuard::new();

        let mut s = self.state.load(Ordering::Relaxed);
        loop {
            if s <= 1 {
                match self.state.compare_exchange(
                    s,
                    usize::MAX,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => {
                        return RwLockWriteGuard {
                            rwlock: self,
                            _interrupt_guard,
                            _phantom: Default::default(),
                        };
                    }
                    Err(e) => {
                        s = e;
                        continue;
                    }
                }
            }

            if s & 1 == 0 {
                match self
                    .state
                    .compare_exchange(s, s + 1, Ordering::Relaxed, Ordering::Relaxed)
                {
                    Ok(_) => (),
                    Err(e) => {
                        s = e;
                        continue;
                    }
                }
            }

            let w = self.writer_wake_counter.load(Ordering::Acquire);
            s = self.state.load(Ordering::Relaxed);

            if s >= 2 {
                while self.writer_wake_counter.load(Ordering::Acquire) == w {
                    hint::spin_loop();

                    #[cfg(loom)]
                    loom::thread::yield_now();
                }
                s = self.state.load(Ordering::Relaxed);
            }

            #[cfg(loom)]
            loom::thread::yield_now();
        }
    }
}

pub struct RwLockReadGuard<'a, T: Send> {
    rwlock: &'a RwLock<T>,
    _interrupt_guard: crate::interrupt_guard::InterruptGuard,
    _phantom: PhantomData<*mut ()>,
}

impl<T: Send> RwLockReadGuard<'_, T> {
    /// unlock read lock
    pub fn unlock(self) {}

    #[cfg(loom)]
    pub fn with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(*const T) -> R,
    {
        self.rwlock.data.with(f)
    }
}

pub struct RwLockWriteGuard<'a, T: Send> {
    rwlock: &'a RwLock<T>,
    _interrupt_guard: crate::interrupt_guard::InterruptGuard,
    _phantom: PhantomData<*mut ()>,
}

impl<T: Send> RwLockWriteGuard<'_, T> {
    /// unlock write lock
    pub fn unlock(self) {}

    #[cfg(loom)]
    pub fn with_mut<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(*mut T) -> R,
    {
        self.rwlock.data.with_mut(f)
    }
}

#[cfg(not(loom))]
impl<T: Send> AsMut<T> for RwLockWriteGuard<'_, T> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut T {
        unsafe { &mut *self.rwlock.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> AsRef<T> for RwLockWriteGuard<'_, T> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        unsafe { &*self.rwlock.data.get() }
    }
}

unsafe impl<T: Send> Sync for RwLock<T> {}
unsafe impl<T: Send> Send for RwLock<T> {}

#[cfg(not(loom))]
impl<T: Send> AsMut<T> for RwLockReadGuard<'_, T> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut T {
        unsafe { &mut *self.rwlock.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> AsRef<T> for RwLockReadGuard<'_, T> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        unsafe { &*self.rwlock.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> Deref for RwLockReadGuard<'_, T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.rwlock.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> Deref for RwLockWriteGuard<'_, T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.rwlock.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> DerefMut for RwLockWriteGuard<'_, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.rwlock.data.get() }
    }
}

/// release read lock
impl<T: Send> Drop for RwLockReadGuard<'_, T> {
    #[inline(always)]
    fn drop(&mut self) {
        if self.rwlock.state.fetch_sub(2, Ordering::Release) == 3 {
            self.rwlock
                .writer_wake_counter
                .fetch_add(1, Ordering::Release);
        }
    }
}

/// release write lock
impl<T: Send> Drop for RwLockWriteGuard<'_, T> {
    #[inline(always)]
    fn drop(&mut self) {
        self.rwlock.state.store(0, Ordering::Release);
        self.rwlock
            .writer_wake_counter
            .fetch_add(1, Ordering::Release);
    }
}

#[cfg(loom)]
impl<'a, T: Send> Deref for RwLockReadGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unimplemented!("loom does not support deref");
    }
}

#[cfg(loom)]
impl<'a, T: Send> Deref for RwLockWriteGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unimplemented!("loom does not support deref");
    }
}

#[cfg(loom)]
impl<'a, T: Send> DerefMut for RwLockWriteGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unimplemented!("loom does not support deref_mut");
    }
}
