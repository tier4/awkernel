use alloc::boxed::Box;
use core::alloc::Layout;
use t4os_lib::delay::wait_forever;

#[alloc_error_handler]
fn on_oom(_layout: Layout) -> ! {
    unwinding::panic::begin_panic(Box::new(()));

    wait_forever();
}

#[cfg(all(any(target_arch = "x86_64", target_arch = "aarch64")))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    unwinding::panic::begin_panic(Box::new(()));
    wait_forever();
}
