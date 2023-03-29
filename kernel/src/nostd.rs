use alloc::boxed::Box;
use awkernel_lib::{delay::wait_forever, heap::TALLOC};
use core::alloc::Layout;

#[alloc_error_handler]
fn on_oom(layout: Layout) -> ! {
    unsafe {
        TALLOC.use_backup();
    }
    log::error!("heap allocation error: {:?}", layout);
    unwinding::panic::begin_panic(Box::new(()));
    wait_forever();
}

#[cfg(any(feature = "x86", feature = "aarch64"))]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    unsafe {
        TALLOC.use_backup();
    }
    log::error!("{}", info);
    unwinding::panic::begin_panic(Box::new(()));
    wait_forever();
}
