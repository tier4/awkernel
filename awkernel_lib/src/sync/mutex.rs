#[cfg(not(feature = "std"))]
type Lock<T> = super::mcs::MCSLock<T>;

#[cfg(not(feature = "std"))]
type LockGuard<'a, T> = super::mcs::MCSLockGuard<'a, T>;

#[cfg(feature = "std")]
type Lock<T> = parking_lot::Mutex<T>;

#[cfg(feature = "std")]
type LockGuard<'a, T> = parking_lot::MutexGuard<'a, T>;

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

    #[cfg(not(feature = "std"))]
    pub fn lock<'a>(&'a self, node: &'a mut MCSNode<T>) -> LockGuard<'a, T> {
        self.mutex.lock(node)
    }

    #[cfg(feature = "std")]
    pub fn lock<'a>(&'a self, _node: &mut MCSNode<T>) -> LockGuard<'a, T> {
        self.mutex.lock()
    }
}

pub use super::mcs::MCSNode;
