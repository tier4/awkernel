use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    pin::Pin,
};

#[cfg(not(loom))]
use core::{
    cell::UnsafeCell,
    hint,
    sync::atomic::{fence, AtomicBool, AtomicPtr, AtomicU64, Ordering},
};

use alloc::boxed::Box;
#[cfg(loom)]
use loom::{
    cell::UnsafeCell,
    hint,
    sync::atomic::{fence, AtomicBool, AtomicPtr, AtomicU64, Ordering},
};

use crate::interrupt::InterruptGuard;

#[cfg(not(loom))]
use crate::cpu::NUM_MAX_CPU;

#[cfg(not(loom))]
static VISIBLE_READERS: [AtomicPtr<()>; NUM_MAX_CPU] =
    array_macro::array![_ => AtomicPtr::new(core::ptr::null_mut()); NUM_MAX_CPU];

#[cfg(not(loom))]
#[inline(always)]
fn get_visible_readers() -> &'static [AtomicPtr<()>] {
    &VISIBLE_READERS
}

#[cfg(loom)]
static mut VISIBLE_READERS_VEC: alloc::vec::Vec<AtomicPtr<()>> = alloc::vec::Vec::new();

#[cfg(loom)]
#[inline(always)]
fn get_visible_readers<'a>() -> &'a [AtomicPtr<()>] {
    unsafe {
        let v = &mut *(&raw mut VISIBLE_READERS_VEC);

        if v.is_empty() {
            for _ in 0..10 {
                v.push(AtomicPtr::new(core::ptr::null_mut()));
            }
        }

        v.as_slice()
    }
}

#[cfg(loom)]
pub fn init_visible_readers<'a>() {
    unsafe {
        let v = &mut *(&raw mut VISIBLE_READERS_VEC);

        if v.is_empty() {
            for _ in 0..10 {
                v.push(AtomicPtr::new(core::ptr::null_mut()));
            }
        }
    }
}

pub struct BravoRwLock<T: Send> {
    inner: Pin<Box<Inner<T>>>,
}

struct Inner<T: Send> {
    rbias: AtomicBool,
    inhibit_until: AtomicU64,
    underlying: super::rwlock::RwLock<()>,
    data: UnsafeCell<T>,
}

impl<T: Send> BravoRwLock<T> {
    pub fn new(v: T) -> BravoRwLock<T> {
        let inner = Inner {
            rbias: AtomicBool::new(false),
            inhibit_until: AtomicU64::new(0),
            underlying: super::rwlock::RwLock::new(()),
            data: UnsafeCell::new(v),
        };

        BravoRwLock {
            inner: Box::pin(inner),
        }
    }

    #[cfg(loom)]
    pub fn read_cpu_id(&self, cpu_id: usize) -> BravoReadGuard<T> {
        let _interrupt_guard = crate::interrupt::InterruptGuard::new();
        self.read_on(cpu_id, _interrupt_guard)
    }

    #[inline(always)]
    fn read_on(&self, cpu_id: usize, interrupt_guard: InterruptGuard) -> BravoReadGuard<T> {
        let inner = self.inner.deref();

        if inner.rbias.load(Ordering::Relaxed) {
            let slot = &get_visible_readers()[cpu_id];
            let l = inner as *const _ as *mut ();

            if slot
                .compare_exchange(
                    core::ptr::null_mut(),
                    l,
                    Ordering::AcqRel,
                    Ordering::Relaxed,
                )
                .is_ok()
            {
                if inner.rbias.load(Ordering::Relaxed) {
                    // recheck
                    // fast path
                    return BravoReadGuard {
                        rwlock: self,
                        guard: None,
                        slot: Some(slot),
                        _interrupt_guard: interrupt_guard,
                        _phantom: PhantomData,
                    };
                }

                // raced - RBias was cleared
                slot.store(core::ptr::null_mut(), Ordering::Relaxed);
            }
        }

        let guard = inner.underlying.read();

        if inner.rbias.load(Ordering::Relaxed) == false
            && crate::delay::uptime() >= inner.inhibit_until.load(Ordering::Relaxed)
        {
            inner.rbias.store(true, Ordering::Relaxed);
        }

        BravoReadGuard {
            rwlock: self,
            guard: Some(guard),
            slot: None,
            _interrupt_guard: interrupt_guard,
            _phantom: PhantomData,
        }
    }

    /// acquire reader lock
    #[inline(always)]
    pub fn read(&self) -> BravoReadGuard<T> {
        let _interrupt_guard = crate::interrupt::InterruptGuard::new();
        let cpu_id = crate::cpu::cpu_id();
        self.read_on(cpu_id, _interrupt_guard)
    }

    /// acquire writer lock
    #[inline(always)]
    pub fn write(&self) -> BravoWriteGuard<T> {
        const N: u64 = 9; // slow-down guard

        let inner = self.inner.deref();

        let guard = inner.underlying.write();

        if inner.rbias.load(Ordering::Relaxed) {
            // revoke bias

            fence(Ordering::SeqCst);

            inner.rbias.store(false, Ordering::Relaxed);
            let start = crate::delay::uptime();
            for reader in get_visible_readers().iter() {
                while reader.load(Ordering::Relaxed) == inner as *const _ as *mut () {
                    hint::spin_loop();

                    #[cfg(loom)]
                    loom::thread::yield_now();
                }
            }

            let now = crate::delay::uptime();

            if now > start {
                inner
                    .inhibit_until
                    .store(now + (now - start) * N, Ordering::Relaxed);
            } else {
                inner.inhibit_until.store(now, Ordering::Relaxed);
            }
        }

        BravoWriteGuard {
            rwlock: self,
            _guard: guard,
            _interrupt_guard: crate::interrupt::InterruptGuard::new(),
            _phantom: PhantomData,
        }
    }
}

pub struct BravoReadGuard<'a, T: Send> {
    rwlock: &'a BravoRwLock<T>,
    guard: Option<super::rwlock::RwLockReadGuard<'a, ()>>,
    slot: Option<&'a AtomicPtr<()>>,
    _interrupt_guard: crate::interrupt::InterruptGuard,
    _phantom: PhantomData<*mut ()>,
}

impl<T: Send> BravoReadGuard<'_, T> {
    /// unlock read lock
    pub fn unlock(self) {}

    #[cfg(loom)]
    pub fn with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(*const T) -> R,
    {
        self.rwlock.inner.data.with(f)
    }
}

pub struct BravoWriteGuard<'a, T: Send> {
    rwlock: &'a BravoRwLock<T>,
    _guard: super::rwlock::RwLockWriteGuard<'a, ()>,
    _interrupt_guard: crate::interrupt::InterruptGuard,
    _phantom: PhantomData<*mut ()>,
}

impl<T: Send> BravoWriteGuard<'_, T> {
    /// unlock write lock
    pub fn unlock(self) {}

    #[cfg(loom)]
    pub fn with_mut<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(*mut T) -> R,
    {
        self.rwlock.inner.data.with_mut(f)
    }
}

#[cfg(not(loom))]
impl<T: Send> AsMut<T> for BravoWriteGuard<'_, T> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut T {
        unsafe { &mut *self.rwlock.inner.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> AsRef<T> for BravoWriteGuard<'_, T> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        unsafe { &*self.rwlock.inner.data.get() }
    }
}

unsafe impl<T: Send> Sync for BravoRwLock<T> {}
unsafe impl<T: Send> Send for BravoRwLock<T> {}

#[cfg(not(loom))]
impl<T: Send> AsMut<T> for BravoReadGuard<'_, T> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut T {
        unsafe { &mut *self.rwlock.inner.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> AsRef<T> for BravoReadGuard<'_, T> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        unsafe { &*self.rwlock.inner.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> Deref for BravoReadGuard<'_, T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.rwlock.inner.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> Deref for BravoWriteGuard<'_, T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.rwlock.inner.data.get() }
    }
}

#[cfg(not(loom))]
impl<T: Send> DerefMut for BravoWriteGuard<'_, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.rwlock.inner.data.get() }
    }
}

/// release read lock
impl<T: Send> Drop for BravoReadGuard<'_, T> {
    #[inline(always)]
    fn drop(&mut self) {
        if let Some(slot) = self.slot {
            slot.store(core::ptr::null_mut(), Ordering::Relaxed);
        } else {
            self.guard.take();
        }
    }
}

#[cfg(loom)]
impl<'a, T: Send> Deref for BravoReadGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unimplemented!("loom does not support deref");
    }
}

#[cfg(loom)]
impl<'a, T: Send> Deref for BravoWriteGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unimplemented!("loom does not support deref");
    }
}

#[cfg(loom)]
impl<'a, T: Send> DerefMut for BravoWriteGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unimplemented!("loom does not support deref_mut");
    }
}
