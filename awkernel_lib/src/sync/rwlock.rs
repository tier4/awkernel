use core::{
    cell::UnsafeCell,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
};

pub struct RwLock<T: Send> {
    rcnt: AtomicUsize,
    wcnt: AtomicUsize,
    lock: AtomicBool,
    data: UnsafeCell<T>,
}

impl<T: Send> RwLock<T> {
    pub const fn new(v: T) -> RwLock<T> {
        RwLock {
            rcnt: AtomicUsize::new(0),
            wcnt: AtomicUsize::new(0),
            lock: AtomicBool::new(false),
            data: UnsafeCell::new(v),
        }
    }

    /// acquire reader lock
    pub fn read(&self) -> RwLockReadGuard<T> {
        loop {
            while self.wcnt.load(Ordering::Relaxed) > 0 {}
            self.rcnt.fetch_add(1, Ordering::Acquire);
            if self.wcnt.load(Ordering::Relaxed) == 0 {
                break;
            }
            self.rcnt.fetch_sub(1, Ordering::Relaxed);
        }

        let _interrupt_guard = crate::interrupt::InterruptGuard::new();

        RwLockReadGuard {
            rwlock: self,
            _interrupt_guard,
            _phantom: Default::default(),
        }
    }

    /// acquire writer lock
    pub fn write(&self) -> RwLockWriteGuard<T> {
        self.wcnt.fetch_add(1, Ordering::Relaxed);
        while self.rcnt.load(Ordering::Relaxed) > 0 {}

        loop {
            while self.lock.load(Ordering::Relaxed) {
                core::hint::spin_loop()
            }
            if self
                .lock
                .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                break;
            }
        }

        let _interrupt_guard = crate::interrupt::InterruptGuard::new();

        RwLockWriteGuard {
            rwlock: self,
            _interrupt_guard,
            _phantom: Default::default(),
        }
    }
}

pub struct RwLockReadGuard<'a, T: Send> {
    rwlock: &'a RwLock<T>,
    _interrupt_guard: crate::interrupt::InterruptGuard,
    _phantom: PhantomData<*mut ()>,
}

impl<'a, T: Send> RwLockReadGuard<'a, T> {
    /// unlock read lock
    pub fn unlock(self) {}
}

pub struct RwLockWriteGuard<'a, T: Send> {
    rwlock: &'a RwLock<T>,
    _interrupt_guard: crate::interrupt::InterruptGuard,
    _phantom: PhantomData<*mut ()>,
}

impl<'a, T: Send> RwLockWriteGuard<'a, T> {
    /// unlock write lock
    pub fn unlock(self) {}
}

unsafe impl<T: Send> Sync for RwLock<T> {}
unsafe impl<T: Send> Send for RwLock<T> {}

impl<'a, T: Send> Deref for RwLockReadGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.rwlock.data.get() }
    }
}

impl<'a, T: Send> Deref for RwLockWriteGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.rwlock.data.get() }
    }
}

impl<'a, T: Send> DerefMut for RwLockWriteGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.rwlock.data.get() }
    }
}

/// release read lock
impl<'a, T: Send> Drop for RwLockReadGuard<'a, T> {
    fn drop(&mut self) {
        self.rwlock.rcnt.fetch_sub(1, Ordering::Release);
    }
}

/// release write lock
impl<'a, T: Send> Drop for RwLockWriteGuard<'a, T> {
    fn drop(&mut self) {
        self.rwlock.lock.store(false, Ordering::Relaxed);
        self.rwlock.wcnt.fetch_sub(1, Ordering::Release);
    }
}
