use alloc::boxed::Box;
use awkernel_lib::{delay::wait_forever, heap::TALLOC};

#[cfg(any(feature = "x86", feature = "aarch64", feature = "rv32"))]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    {
        let _guard = TALLOC.save();
        unsafe { TALLOC.use_primary_then_backup() };
        log::error!("panic: {}", info);
    }

    unwinding::panic::begin_panic(Box::new(()));
    wait_forever();
}
