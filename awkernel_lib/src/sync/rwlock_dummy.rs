//! This is a dummy implementation of `RwLock` for loom.

use core::{
    cell::UnsafeCell,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

pub struct RwLock<T: Send> {
    data: UnsafeCell<T>,
}

impl<T: Send> RwLock<T> {
    pub const fn new(v: T) -> RwLock<T> {
        RwLock {
            data: UnsafeCell::new(v),
        }
    }

    /// acquire reader lock
    pub fn read(&self) -> RwLockReadGuard<T> {
        RwLockReadGuard {
            rwlock: self,
            _phantom: Default::default(),
        }
    }

    /// acquire writer lock
    pub fn write(&self) -> RwLockWriteGuard<T> {
        RwLockWriteGuard {
            rwlock: self,
            _phantom: Default::default(),
        }
    }
}

pub struct RwLockReadGuard<'a, T: Send> {
    rwlock: &'a RwLock<T>,
    _phantom: PhantomData<*mut ()>,
}

impl<'a, T: Send> RwLockReadGuard<'a, T> {
    /// unlock read lock
    pub fn unlock(self) {}
}

pub struct RwLockWriteGuard<'a, T: Send> {
    rwlock: &'a RwLock<T>,
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
