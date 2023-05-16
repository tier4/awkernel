use core::{
    cell::UnsafeCell,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::null_mut,
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
    pub fn new() -> Self {
        MCSNode {
            next: AtomicPtr::new(null_mut()),
            locked: AtomicBool::new(false),
        }
    }
}

impl<T: Send> MCSLock<T> {
    pub const fn new(v: T) -> MCSLock<T> {
        MCSLock {
            last: AtomicPtr::new(null_mut()),
            data: UnsafeCell::new(v),
        }
    }

    /// acquire lock
    pub fn lock<'a>(&'a self, node: &'a mut MCSNode<T>) -> MCSLockGuard<T> {
        node.next = AtomicPtr::new(null_mut());
        node.locked = AtomicBool::new(false);

        let _interrupt_guard = crate::interrupt::InterruptGuard::new();

        // set myself as the last node
        let guard = MCSLockGuard {
            node,
            mcs_lock: self,
            _interrupt_guard,
            _phantom: Default::default(),
        };

        let ptr = guard.node as *mut MCSNode<T>;
        let prev = self.last.swap(ptr, Ordering::Relaxed);

        // if prev is null then nobody is trying to acquire lock,
        // otherwise enqueue myself
        if !prev.is_null() {
            // set acquiring lock
            guard.node.locked.store(true, Ordering::Relaxed);

            // enqueue myself
            let prev = unsafe { &*prev };
            prev.next.store(ptr, Ordering::Relaxed);

            // spin until other thread set locked false
            while guard.node.locked.load(Ordering::Relaxed) {
                core::hint::spin_loop()
            }
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
    _interrupt_guard: crate::interrupt::InterruptGuard,
    _phantom: PhantomData<*mut ()>,
}

impl<'a, T: Send> Drop for MCSLockGuard<'a, T> {
    fn drop(&mut self) {
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
        }

        // other thread is entering lock and wait the execution
        while self.node.next.load(Ordering::Relaxed).is_null() {
            core::hint::spin_loop()
        }

        // make next thread executable
        let next = unsafe { &mut *self.node.next.load(Ordering::Relaxed) };
        next.locked.store(false, Ordering::Release);
    }
}

impl<'a, T: Send> Deref for MCSLockGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.mcs_lock.data.get() }
    }
}

impl<'a, T: Send> DerefMut for MCSLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.mcs_lock.data.get() }
    }
}
