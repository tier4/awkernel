use core::{
    cell::UnsafeCell,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicBool, Ordering},
};

pub struct SpinLock<T> {
    lock_var: AtomicBool,
    data: UnsafeCell<T>,
}

unsafe impl<T: Send> Sync for SpinLock<T> {}
unsafe impl<T: Send> Send for SpinLock<T> {}

impl<T> SpinLock<T> {
    pub const fn new(v: T) -> Self {
        SpinLock {
            lock_var: AtomicBool::new(false),
            data: UnsafeCell::new(v),
        }
    }

    #[inline(always)]
    pub fn try_lock(&self) -> Option<SpinLockGuard<T>> {
        let _interrupt_guard = crate::interrupt_guard::InterruptGuard::new();
        if self
            .lock_var
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            Some(SpinLockGuard {
                spin_lock: self,
                _interrupt_guard,
                _phantom: PhantomData,
            })
        } else {
            None
        }
    }

    #[inline(always)]
    pub fn lock(&self) -> SpinLockGuard<T> {
        let _interrupt_guard = loop {
            if !self.lock_var.load(Ordering::Relaxed) {
                let interrupt_guard = crate::interrupt_guard::InterruptGuard::new();
                if self
                    .lock_var
                    .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok()
                {
                    break interrupt_guard;
                };
            }
        };

        SpinLockGuard {
            spin_lock: self,
            _interrupt_guard,
            _phantom: PhantomData,
        }
    }
}

pub struct SpinLockGuard<'a, T> {
    spin_lock: &'a SpinLock<T>,
    _interrupt_guard: crate::interrupt_guard::InterruptGuard,
    _phantom: PhantomData<*mut ()>,
}

impl<T> Drop for SpinLockGuard<'_, T> {
    #[inline(always)]
    fn drop(&mut self) {
        self.spin_lock.lock_var.store(false, Ordering::Release);
    }
}

impl<T: Send> Deref for SpinLockGuard<'_, T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.spin_lock.data.get() }
    }
}

impl<T: Send> DerefMut for SpinLockGuard<'_, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.spin_lock.data.get() }
    }
}

impl<T: Send> AsMut<T> for SpinLockGuard<'_, T> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut T {
        unsafe { &mut *self.spin_lock.data.get() }
    }
}

impl<T: Send> AsRef<T> for SpinLockGuard<'_, T> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        unsafe { &*self.spin_lock.data.get() }
    }
}
