use awkernel_async_lib::{
    cpu_counter,
    task::perf::{add_task_end, add_task_start},
};
use awkernel_lib::{
    arch::aarch64::exception_saved_regs::Context, console::unsafe_puts, delay::wait_forever,
    interrupt,
};
use core::str::from_utf8_unchecked;

const _ESR_EL1_EC_MASK: u64 = 0b111111 << 26;
const _ESR_EL1_EC_UNKNOWN: u64 = 0b000000 << 26;
const _ESR_EL1_EC_WFI_OR_WFE: u64 = 0b000001 << 26;
const _ESR_EL1_EC_SVC32: u64 = 0b010001 << 26;
const _ESR_EL1_EC_SVC64: u64 = 0b010101 << 26;
const _ESR_LE1_EC_DATA: u64 = 0b100100 << 26;
const _ESR_LE1_EC_DATA_KERN: u64 = 0b100101 << 26;

#[no_mangle]
pub extern "C" fn handle_data_abort() {
    unsafe { unsafe_puts("data abort\r\n") };

    let sp = awkernel_aarch64::get_sp();
    unsafe { unsafe_puts("SP  = 0x") };
    print_hex(sp);
    unsafe { unsafe_puts("\r\n") };

    let elr = awkernel_aarch64::elr_el1::get();
    unsafe { unsafe_puts("ELR = 0x") };
    print_hex(elr);
    unsafe { unsafe_puts("\r\n") };

    let far = awkernel_aarch64::far_el1::get();
    unsafe { unsafe_puts("FAR = 0x") };
    print_hex(far);
    unsafe { unsafe_puts("\r\n") };
}

fn print_hex(num: u64) {
    let hex = to_hex(num);

    let mut msg = [b'0'];

    for n in hex.iter().rev() {
        msg[0] = *n;

        unsafe {
            let msg = from_utf8_unchecked(&msg);
            unsafe_puts(msg);
        };
    }
}

fn to_hex(mut num: u64) -> [u8; 16] {
    let mut result = [b'0'; 16];

    let mut i = 0;
    while num > 0 {
        let n = num & 0xf;

        result[i] = if n < 10 {
            b'0' + n as u8
        } else {
            b'a' + (n as u8 - 10)
        };

        num /= 16;
        i += 1;
    }

    result
}

//------------------------------------------------------------------------------

// EL2

// from the current EL using the current SP0
#[no_mangle]
pub extern "C" fn curr_el_sp0_sync_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn curr_el_sp0_irq_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn curr_el_sp0_fiq_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn curr_el_sp0_serror_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn curr_el_spx_sync_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn curr_el_spx_irq_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn curr_el_spx_fiq_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn curr_el_spx_serror_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

// from lower EL (AArch64)
#[no_mangle]
pub extern "C" fn lower_el_aarch64_sync_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch64_irq_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch64_fiq_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch64_serror_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

// from lower EL (AArch32)
#[no_mangle]
pub extern "C" fn lower_el_aarch32_sync_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch32_irq_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch32_fiq_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch32_serror_el2(_ctx: *mut Context, _sp: usize, _esr: usize) {}

//------------------------------------------------------------------------------

// EL1

// from the current EL using the SP_EL0
#[no_mangle]
pub extern "C" fn curr_el_sp0_sync_el1(ctx: *mut Context, _sp: usize, esr: usize) {
    let r = unsafe { &*ctx };
    log::debug!(
        r#"EL1 exception: SP0 Sync
ELR  = 0x{:x}
SPSR = 0x{:x}
ESR  = 0x{:x}
"#,
        r.elr,
        r.spsr,
        esr
    );

    wait_forever();
}

#[no_mangle]
pub extern "C" fn curr_el_sp0_irq_el1(ctx: *mut Context, _sp: usize, esr: usize) {
    let r = unsafe { &*ctx };
    log::debug!(
        r#"EL1 exception: SP0 IRQ
ELR  = 0x{:x}
SPSR = 0x{:x}
ESR  = 0x{:x}
"#,
        r.elr,
        r.spsr,
        esr
    );

    wait_forever();
}

#[no_mangle]
pub extern "C" fn curr_el_sp0_fiq_el1(ctx: *mut Context, _sp: usize, esr: usize) {
    let r = unsafe { &*ctx };
    log::debug!(
        r#"EL1 exception: SP0 FIQ
ELR  = 0x{:x}
SPSR = 0x{:x}
ESR  = 0x{:x}
"#,
        r.elr,
        r.spsr,
        esr
    );

    wait_forever();
}

#[no_mangle]
pub extern "C" fn curr_el_sp0_serror_el1(ctx: *mut Context, _sp: usize, esr: usize) {
    let r = unsafe { &*ctx };
    log::debug!(
        r#"EL1 exception: SP0 SERROR
ELR  = 0x{:x}
SPSR = 0x{:x}
ESR  = 0x{:x}
"#,
        r.elr,
        r.spsr,
        esr
    );

    wait_forever();
}

// from the current EL using the SP_EL1
#[no_mangle]
pub extern "C" fn curr_el_spx_sync_el1(ctx: *mut Context, _sp: usize, esr: usize) {
    let r = unsafe { &*ctx };
    log::debug!(
        r#"EL1 exception: SPX Sync
ELR  = 0x{:x}
SPSR = 0x{:x}
ESR  = 0x{:x}
"#,
        r.elr,
        r.spsr,
        esr
    );

    // wait_forever();
    interrupt::handle_irqs();
}

#[no_mangle]
pub extern "C" fn curr_el_spx_irq_el1(_ctx: *mut Context, _sp: usize, _esr: usize) {
    add_task_end(awkernel_lib::cpu::cpu_id(), cpu_counter());
    interrupt::handle_irqs();
    add_task_start(awkernel_lib::cpu::cpu_id(), cpu_counter());
}

#[no_mangle]
pub extern "C" fn curr_el_spx_fiq_el1(ctx: *mut Context, _sp: usize, esr: usize) {
    let r = unsafe { &*ctx };
    log::debug!(
        r#"EL1 exception: SPX FIQ
ELR  = 0x{:x}
SPSR = 0x{:x}
ESR  = 0x{:x}
"#,
        r.elr,
        r.spsr,
        esr
    );

    wait_forever();
}

#[no_mangle]
pub extern "C" fn curr_el_spx_serror_el1(ctx: *mut Context, _sp: usize, esr: usize) {
    let r = unsafe { &*ctx };
    log::debug!(
        r#"EL1 exception: SPX SERROR
ELR  = 0x{:x}
SPSR = 0x{:x}
ESR  = 0x{:x}
"#,
        r.elr,
        r.spsr,
        esr
    );

    wait_forever();
}

// from lower EL (AArch64)
#[no_mangle]
pub extern "C" fn lower_el_aarch64_sync_el1(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch64_irq_el1(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch64_fiq_el1(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch64_serror_el1(_ctx: *mut Context, _sp: usize, _esr: usize) {}

// from lower EL (AArch32)
#[no_mangle]
pub extern "C" fn lower_el_aarch32_sync_el1(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch32_irq_el1(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch32_fiq_el1(_ctx: *mut Context, _sp: usize, _esr: usize) {}

#[no_mangle]
pub extern "C" fn lower_el_aarch32_serror_el1(_ctx: *mut Context, _sp: usize, _esr: usize) {}
