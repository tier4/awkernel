/// An `Arc` like data structure under Bare Metal Mode,
/// you can directly use it without `unsafe` keyword.
use core::cell::{RefCell, RefMut};

/// Safety
/// Only use it in uniprocessor
pub struct SafeArc<T> {
    inner: RefCell<T>,
}

unsafe impl<T> Sync for SafeArc<T> {}

impl<T> SafeArc<T> {
    pub unsafe fn new(value: T) -> Self {
        Self {
            inner: RefCell::new(value),
        }
    }

    pub fn exclusive_access(&self) -> RefMut<'_, T> {
        self.inner.borrow_mut()
    }
}
