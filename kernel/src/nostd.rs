use alloc::boxed::Box;
use awkernel_lib::{delay::wait_forever, heap::TALLOC};

use core::ffi::c_void;
use unwinding::abi::{UnwindContext, UnwindReasonCode, _Unwind_Backtrace, _Unwind_GetIP};

#[cfg(any(
    feature = "x86",
    feature = "aarch64",
    feature = "rv32",
    feature = "rv64"
))]
fn stack_trace() {
    struct CallbackData {
        counter: usize,
    }

    extern "C" fn callback(unwind_ctx: &UnwindContext<'_>, arg: *mut c_void) -> UnwindReasonCode {
        let data = unsafe { &mut *(arg as *mut CallbackData) };
        data.counter += 1;

        // TODO: Prints detailed debugging information
        let addr = _Unwind_GetIP(unwind_ctx);
        log::info!("{:02}:\t{:#016x} - UNKNOWN", data.counter, addr);

        UnwindReasonCode::NO_REASON
    }

    let mut data = CallbackData { counter: 0 };
    _Unwind_Backtrace(callback, &mut data as *mut _ as _);
}

#[cfg(any(
    feature = "x86",
    feature = "aarch64",
    feature = "rv32",
    feature = "rv64"
))]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    {
        let _guard = TALLOC.save();
        unsafe { TALLOC.use_primary_then_backup() };
        log::error!("panic: {}", info);
    }

    awkernel_async_lib::task::panicking();
    stack_trace();
    unwinding::panic::begin_panic(Box::new(()));
    wait_forever();
}
