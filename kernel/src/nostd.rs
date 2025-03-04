use alloc::boxed::Box;
use awkernel_lib::{delay::wait_forever, heap::TALLOC};

use core::ffi::c_void;
use unwinding::abi::{UnwindContext, UnwindReasonCode, _Unwind_Backtrace, _Unwind_GetIP};

// Base address and size of each debug section
unsafe extern "C" {
    static __debug_abbrev_start: u8;
    static __debug_abbrev_size: u8;
    static __debug_info_start: u8;
    static __debug_info_size: u8;
    static __debug_aranges_start: u8;
    static __debug_aranges_size: u8;
    static __debug_ranges_start: u8;
    static __debug_ranges_size: u8;
    static __debug_str_start: u8;
    static __debug_str_size: u8;
    static __debug_line_start: u8;
    static __debug_line_size: u8;
}

#[cfg(any(
    feature = "x86",
    feature = "aarch64",
    feature = "rv32",
    feature = "rv64"
))]
#[cfg(not(feature = "debug"))]
fn stack_trace() {
    struct CallbackData {
        counter: usize,
    }

    extern "C" fn callback(unwind_ctx: &UnwindContext<'_>, arg: *mut c_void) -> UnwindReasonCode {
        let data = unsafe { &mut *(arg as *mut CallbackData) };

        data.counter += 1;

        let addr = _Unwind_GetIP(unwind_ctx);
        log::info!("{}:\t{:#016x} - UNKNOWN", data.counter, addr);
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
#[cfg(feature = "debug")]
fn stack_trace() {
    struct CallbackData<'a> {
        counter: usize,
        context: addr2line::Context<gimli::EndianSlice<'a, gimli::LittleEndian>>,
    }

    extern "C" fn callback(unwind_ctx: &UnwindContext<'_>, arg: *mut c_void) -> UnwindReasonCode {
        let data = unsafe { &mut *(arg as *mut CallbackData) };

        data.counter += 1;

        let addr = _Unwind_GetIP(unwind_ctx);
        let mut frames = data
            .context
            .find_frames(addr as u64)
            .skip_all_loads()
            .unwrap();

        while let Ok(Some(frame)) = frames.next() {
            if let Some(name) = frame.function {
                let location = frame.location.unwrap();
                log::info!(
                    "{}:\t{:#016x} - {}\n\t\tat {}:{}:{}",
                    data.counter,
                    addr,
                    name.demangle().unwrap(),
                    location.file.unwrap(),
                    location.line.unwrap_or(0),
                    location.column.unwrap_or(0)
                )
            } else {
                log::info!("{}:\t{:#016x} - UNKNOWN", data.counter, addr);
            }
        }
        UnwindReasonCode::NO_REASON
    }

    let endian = gimli::LittleEndian;
    let loader =
            |id: gimli::SectionId| -> Result<gimli::EndianSlice<'_, gimli::LittleEndian>, gimli::Error> {
                unsafe {
                    Ok(match id {
                        gimli::SectionId::DebugAbbrev => gimli::EndianSlice::new(
                            core::slice::from_raw_parts(
                                &raw const __debug_abbrev_start,
                                &raw const __debug_abbrev_size as usize,
                            ),
                            endian,
                        ),
                        gimli::SectionId::DebugInfo => gimli::EndianSlice::new(
                            core::slice::from_raw_parts(
                                &raw const __debug_info_start,
                                &raw const __debug_info_size as usize,
                            ),
                            endian,
                        ),
                        gimli::SectionId::DebugAranges => gimli::EndianSlice::new(
                            core::slice::from_raw_parts(
                                &raw const __debug_aranges_start,
                                &raw const __debug_aranges_size as usize,
                            ),
                            endian,
                        ),
                        gimli::SectionId::DebugRanges => gimli::EndianSlice::new(
                            core::slice::from_raw_parts(
                                &raw const __debug_ranges_start,
                                &raw const __debug_ranges_size as usize,
                            ),
                            endian,
                        ),
                        gimli::SectionId::DebugStr => gimli::EndianSlice::new(
                            core::slice::from_raw_parts(
                                &raw const __debug_str_start,
                                &raw const __debug_str_size as usize,
                            ),
                            endian,
                        ),
                        gimli::SectionId::DebugLine => gimli::EndianSlice::new(
                            core::slice::from_raw_parts(
                                &raw const __debug_line_start,
                                &raw const __debug_line_size as usize,
                            ),
                            endian,
                        ),
                        _ => gimli::EndianSlice::new(&[], endian),
                    })
                }
            };

    let dwarf = gimli::Dwarf::load(loader).unwrap();
    let context = addr2line::Context::from_dwarf(dwarf).unwrap();
    let mut data = CallbackData {
        counter: 0,
        context,
    };
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
