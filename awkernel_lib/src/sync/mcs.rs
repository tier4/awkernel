use core::{
    cell::UnsafeCell,
    mem::transmute,
    ops::{Deref, DerefMut},
    ptr::{null_mut, read_volatile, write_volatile},
    sync::atomic::{fence, AtomicBool, AtomicPtr, Ordering},
};

use crate::cpu;

static mut MCS_NODES: [*mut MCSNode; 1024] = [null_mut(); 1024];

pub struct MCSLock<T> {
    last: AtomicPtr<MCSNode>,
    data: UnsafeCell<T>,
}

pub struct MCSNode {
    next: AtomicPtr<MCSNode>,
    locked: AtomicBool,
}

impl Default for MCSNode {
    fn default() -> Self {
        Self::new()
    }
}

impl MCSNode {
    pub fn new() -> MCSNode {
        MCSNode {
            next: AtomicPtr::new(null_mut()),
            locked: AtomicBool::new(false),
        }
    }
}

impl<T> MCSLock<T> {
    pub const fn new(v: T) -> MCSLock<T> {
        MCSLock {
            last: AtomicPtr::new(null_mut()),
            data: UnsafeCell::new(v),
        }
    }

    /// acquire lock
    pub fn lock<'a>(&'a self) -> MCSLockGuard<T> {
        let node = unsafe { get_node() };

        node.next = AtomicPtr::new(null_mut());
        node.locked = AtomicBool::new(false);

        let _interrupt_guard = crate::interrupt::InterruptGuard::new();

        // set myself as the last node
        let guard = MCSLockGuard {
            node,
            mcs_lock: self,
            _interrupt_guard,
        };

        let ptr = guard.node as *mut MCSNode;
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

unsafe impl<T> Sync for MCSLock<T> {}
unsafe impl<T> Send for MCSLock<T> {}

pub struct MCSLockGuard<'a, T> {
    node: &'a mut MCSNode,
    mcs_lock: &'a MCSLock<T>,
    _interrupt_guard: crate::interrupt::InterruptGuard,
}

impl<'a, T> Drop for MCSLockGuard<'a, T> {
    fn drop(&mut self) {
        // if next node is null and self is the last node
        // set the last node to null
        if self.node.next.load(Ordering::Relaxed).is_null() {
            let ptr = self.node as *mut MCSNode;
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

impl<'a, T> Deref for MCSLockGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.mcs_lock.data.get() }
    }
}

impl<'a, T> DerefMut for MCSLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.mcs_lock.data.get() }
    }
}

pub(crate) unsafe fn init_mcs_node(node: *mut MCSNode) {
    write_volatile(&mut MCS_NODES[cpu::cpu_id()], node);
}

#[inline]
unsafe fn get_node() -> &'static mut MCSNode {
    let ptr = read_volatile(&MCS_NODES[cpu::cpu_id()]);
    assert!(!ptr.is_null());
    transmute(ptr)
}
