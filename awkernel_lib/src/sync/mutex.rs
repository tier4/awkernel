//! # Mutex and LockGuard Types
//!
//! The `Mutex` and `LockGuard` types in this module provide a way to manage concurrent access to shared resources.
//! These types have different implementations depending on whether the `std` feature is enabled or not.
//! When the `std` feature is enabled, it uses `parking_lot::Mutex` for efficient locking.
//! When the `std` feature is disabled, it falls back to using `super::mcs::MCSLock`.

#[cfg(all(not(feature = "std"), not(feature = "spinlock")))]
type Lock<T> = super::mcs::MCSLock<T>;

#[cfg(all(not(feature = "std"), feature = "spinlock"))]
type Lock<T> = super::spinlock::SpinLock<T>;

#[cfg(all(not(feature = "std"), not(feature = "spinlock")))]
pub type LockGuard<'a, T> = super::mcs::MCSLockGuard<'a, T>;

#[cfg(all(not(feature = "std"), feature = "spinlock"))]
pub type LockGuard<'a, T> = super::spinlock::SpinLockGuard<'a, T>;

#[cfg(feature = "std")]
type Lock<T> = parking_lot::Mutex<T>;

#[cfg(feature = "std")]
pub type LockGuard<'a, T> = parking_lot::MutexGuard<'a, T>;

/// A mutual exclusion primitive that provides safe concurrent access to the inner data.
///
/// The `Mutex` type can be used to ensure that only one thread can access the data at a time.
///
/// It has different implementations depending on whether the `std` feature is enabled or not.
/// When the `std` feature is enabled, it uses `parking_lot::Mutex` for efficient locking.
/// When the `std` feature is disabled, it falls back to using `super::mcs::MCSLock`.
///
/// # Example
///
/// ```
/// use awkernel_lib::sync::mutex::{MCSNode, Mutex};
/// use std::{thread, sync::Arc};
///
/// let data = Arc::new(Mutex::new(0));
///
/// let handles: Vec<_> = (0..10).map(|_| {
///     let data = data.clone();
///     thread::spawn(move || {
///         // Lock the data to access the shared resource.
///         let mut node = MCSNode::new();
///         let mut guard = data.lock(&mut node);
///         *guard += 1;
///     })
/// }).collect();
///
/// for handle in handles {
///     handle.join().unwrap();
/// }
///
/// // Since only one thread can access the data at a time, the final value will be 10.
/// let mut node = MCSNode::new();
/// assert_eq!(*data.lock(&mut node), 10);
/// ```
pub struct Mutex<T: Send> {
    #[cfg(not(std))]
    mutex: Lock<T>,
}

impl<T: Send> Mutex<T> {
    pub const fn new(v: T) -> Self {
        Self {
            mutex: Lock::new(v),
        }
    }

    #[cfg(all(not(feature = "std"), not(feature = "spinlock")))]
    #[inline(always)]
    pub fn lock<'a>(&'a self, node: &'a mut MCSNode<T>) -> LockGuard<'a, T> {
        self.mutex.lock(node)
    }

    #[cfg(all(not(feature = "std"), feature = "spinlock"))]
    #[inline(always)]
    pub fn lock<'a>(&'a self, _node: &'a mut MCSNode<T>) -> LockGuard<'a, T> {
        self.mutex.lock()
    }

    #[cfg(feature = "std")]
    #[inline(always)]
    pub fn lock<'a>(&'a self, _node: &mut MCSNode<T>) -> LockGuard<'a, T> {
        self.mutex.lock()
    }

    #[cfg(all(not(feature = "std"), not(feature = "spinlock")))]
    #[inline(always)]
    pub fn try_lock<'a>(&'a self, node: &'a mut MCSNode<T>) -> Option<LockGuard<'a, T>> {
        self.mutex.try_lock(node)
    }

    #[cfg(all(not(feature = "std"), feature = "spinlock"))]
    #[inline(always)]
    pub fn try_lock<'a>(&'a self, _node: &'a mut MCSNode<T>) -> Option<LockGuard<'a, T>> {
        self.mutex.try_lock()
    }

    #[cfg(feature = "std")]
    #[inline(always)]
    pub fn try_lock<'a>(&'a self, _node: &mut MCSNode<T>) -> Option<LockGuard<'a, T>> {
        self.mutex.try_lock()
    }
}

pub use super::mcs::MCSNode;
