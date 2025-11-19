use core::any::Any;

#[cfg(feature = "std")]
pub fn catch_unwind<F, R>(f: F) -> Result<R, Box<(dyn Any + Send + 'static)>>
where
    F: FnOnce() -> R,
{
    use core::panic::AssertUnwindSafe;

    std::panic::catch_unwind(AssertUnwindSafe(f))
}

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

#[cfg(not(feature = "std"))]
pub fn catch_unwind<F, R>(f: F) -> Result<R, Box<dyn Any + Send + 'static>>
where
    F: FnOnce() -> R,
{
    use core::panic::AssertUnwindSafe;

    unwinding::panic::catch_unwind(AssertUnwindSafe(f))
}
