use core::{marker::PhantomData, ptr::null_mut};

#[cfg(not(loom))]
use core::{
    cell::UnsafeCell,
    hint,
    ops::{Deref, DerefMut},
    sync::atomic::{fence, AtomicBool, AtomicPtr, Ordering},
};

#[cfg(loom)]
use loom::{
    cell::UnsafeCell,
    hint,
    sync::atomic::{fence, AtomicBool, AtomicPtr, Ordering},
};

pub struct MCSLock<T: Send> {
    last: AtomicPtr<MCSNode<T>>,
    data: UnsafeCell<T>,
}

pub struct MCSNode<T> {
    next: AtomicPtr<MCSNode<T>>,
    locked: AtomicBool,
}

impl<T> Default for MCSNode<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> MCSNode<T> {
    #[inline(always)]
    pub fn new() -> Self {
        MCSNode {
            next: AtomicPtr::new(null_mut()),
            locked: AtomicBool::new(false),
        }
    }
}

impl<T: Send> MCSLock<T> {
    #[cfg(not(loom))]
    pub const fn new(v: T) -> MCSLock<T> {
        MCSLock {
            last: AtomicPtr::new(null_mut()),
            data: UnsafeCell::new(v),
        }
    }

    #[cfg(loom)]
    pub fn new(v: T) -> MCSLock<T> {
        MCSLock {
            last: AtomicPtr::new(null_mut()),
            data: UnsafeCell::new(v),
        }
    }

    #[inline(always)]
    pub fn try_lock<'a>(&'a self, node: &'a mut MCSNode<T>) -> Option<MCSLockGuard<'a, T>> {
        node.next.store(null_mut(), Ordering::Relaxed);
        node.locked.store(false, Ordering::Relaxed);

        let _interrupt_guard = crate::interrupt_guard::InterruptGuard::new();

        // set myself as the last node
        let mut guard = MCSLockGuard {
            node,
            mcs_lock: self,
            need_unlock: true,
            _interrupt_guard,
            _phantom: PhantomData,
        };

        let ptr = guard.node as *mut MCSNode<T>;

        if self
            .last
            .compare_exchange(null_mut(), ptr, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            Some(guard)
        } else {
            guard.need_unlock = false;
            None
        }
    }

    /// acquire lock
    #[inline(always)]
    pub fn lock<'a>(&'a self, node: &'a mut MCSNode<T>) -> MCSLockGuard<'a, T> {
        node.next.store(null_mut(), Ordering::Relaxed);
        node.locked.store(false, Ordering::Relaxed);

        let _interrupt_guard = crate::interrupt_guard::InterruptGuard::new();

        // set myself as the last node
        let guard = MCSLockGuard {
            node,
            mcs_lock: self,
            need_unlock: true,
            _interrupt_guard,
            _phantom: Default::default(),
        };

        let ptr = guard.node as *mut MCSNode<T>;
        let prev = self.last.swap(ptr, Ordering::AcqRel);

        // if prev is null then nobody is trying to acquire lock
        if prev.is_null() {
            return guard;
        }

        // enqueue myself
        let prev = unsafe { &*prev };
        prev.next.store(ptr, Ordering::Release);

        // spin until other thread sets locked true
        while !guard.node.locked.load(Ordering::Relaxed) {
            hint::spin_loop();

            #[cfg(loom)]
            loom::thread::yield_now();
        }
        fence(Ordering::Acquire);

        guard
    }
}

unsafe impl<T: Send> Sync for MCSLock<T> {}
unsafe impl<T: Send> Send for MCSLock<T> {}

pub struct MCSLockGuard<'a, T: Send> {
    node: &'a mut MCSNode<T>,
    mcs_lock: &'a MCSLock<T>,
    need_unlock: bool,
    _interrupt_guard: crate::interrupt_guard::InterruptGuard,
    _phantom: PhantomData<*mut ()>,
}

impl<T: Send> MCSLockGuard<'_, T> {
    #[cfg(loom)]
    pub fn with_mut<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(*mut T) -> R,
    {
        self.mcs_lock.data.with_mut(f)
    }
}

impl<T: Send> Drop for MCSLockGuard<'_, T> {
    #[inline(always)]
    fn drop(&mut self) {
        if !self.need_unlock {
            return;
        }

        // if next node is null and self is the last node
        // set the last node to null
        if self.node.next.load(Ordering::Relaxed).is_null() {
            let ptr = self.node as *mut MCSNode<T>;
            if self
                .mcs_lock
                .last
                .compare_exchange(ptr, null_mut(), Ordering::Release, Ordering::Relaxed)
                .is_ok()
            {
                return;
            }

            // other thread is entering lock and wait the execution
            while self.node.next.load(Ordering::Relaxed).is_null() {
                hint::spin_loop();

                #[cfg(loom)]
                loom::thread::yield_now();
            }
        }

        // make next thread executable
        let next = unsafe { &mut *self.node.next.load(Ordering::Acquire) };
        next.locked.store(true, Ordering::Release);
    }
}

#[cfg(not(loom))]
impl<T: Send> Deref for MCSLockGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.mcs_lock.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> DerefMut for MCSLockGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.mcs_lock.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> AsMut<T> for MCSLockGuard<'_, T> {
    fn as_mut(&mut self) -> &mut T {
        unsafe { &mut *self.mcs_lock.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> AsRef<T> for MCSLockGuard<'_, T> {
    fn as_ref(&self) -> &T {
        unsafe { &*self.mcs_lock.data.get() }
    }
}
