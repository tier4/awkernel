#[cfg(not(feature = "std"))]
type Lock<T> = super::mcs::MCSLock<T>;

#[cfg(not(feature = "std"))]
type LockGuard<'a, T> = super::mcs::MCSLockGuard<'a, T>;

#[cfg(feature = "std")]
type Lock<T> = std::sync::Mutex<T>;

#[cfg(feature = "std")]
type LockGuard<'a, T> = std::sync::MutexGuard<'a, T>;

pub struct Mutex<T> {
    #[cfg(not(std))]
    mutex: Lock<T>,
}

impl<T> Mutex<T> {
    pub const fn new(v: T) -> Self {
        Self {
            mutex: Lock::new(v),
        }
    }

    #[cfg(not(feature = "std"))]
    pub fn lock<'a>(&'a self) -> LockGuard<'a, T> {
        self.mutex.lock()
    }

    #[cfg(feature = "std")]
    pub fn lock<'a>(&'a self) -> LockGuard<'a, T> {
        self.mutex.lock().unwrap()
    }
}

#[cfg(not(feature = "std"))]
pub use super::mcs::MCSNode;

#[cfg(not(feature = "std"))]
pub unsafe fn init_mcs_node(node: *mut MCSNode) {
    super::mcs::init_mcs_node(node)
}
