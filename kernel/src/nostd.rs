use alloc::boxed::Box;
use awkernel_lib::delay::wait_forever;
use core::alloc::Layout;

#[alloc_error_handler]
fn on_oom(_layout: Layout) -> ! {
    unwinding::panic::begin_panic(Box::new(()));

    wait_forever();
}

#[cfg(any(feature = "x86", feature = "aarch64"))]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    log::error!("{}", info);
    unwinding::panic::begin_panic(Box::new(()));
    wait_forever();
}
