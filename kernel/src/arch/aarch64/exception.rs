use awkernel_lib::{arch::aarch64::context::all_regs::AllContext, delay::wait_forever, interrupt};

const _ESR_EL1_EC_MASK: u64 = 0b111111 << 26;
const _ESR_EL1_EC_UNKNOWN: u64 = 0b000000 << 26;
const _ESR_EL1_EC_WFI_OR_WFE: u64 = 0b000001 << 26;
const _ESR_EL1_EC_SVC32: u64 = 0b010001 << 26;
const _ESR_EL1_EC_SVC64: u64 = 0b010101 << 26;
const _ESR_LE1_EC_DATA: u64 = 0b100100 << 26;
const _ESR_LE1_EC_DATA_KERN: u64 = 0b100101 << 26;

//------------------------------------------------------------------------------

// EL2

// from the current EL using the current SP0
#[no_mangle]
pub fn curr_el_sp0_sync_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn curr_el_sp0_irq_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn curr_el_sp0_fiq_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn curr_el_sp0_serror_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn curr_el_spx_sync_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn curr_el_spx_irq_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn curr_el_spx_fiq_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn curr_el_spx_serror_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

// from lower EL (AArch64)
#[no_mangle]
pub fn lower_el_aarch64_sync_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch64_irq_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch64_fiq_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch64_serror_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

// from lower EL (AArch32)
#[no_mangle]
pub fn lower_el_aarch32_sync_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch32_irq_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch32_fiq_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch32_serror_el2(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

//------------------------------------------------------------------------------

// EL1

// from the current EL using the SP_EL0
#[no_mangle]
pub fn curr_el_sp0_sync_el1(ctx: *mut AllContext, _sp: usize, esr: usize) {
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

    wait_forever();
}

#[no_mangle]
pub fn curr_el_sp0_irq_el1(_ctx: *mut AllContext, _sp: usize, _esr: usize) {
    interrupt::handle_irqs();
}

#[no_mangle]
pub fn curr_el_sp0_fiq_el1(_ctx: *mut AllContext, _sp: usize, _esr: usize) {
    loop {}
}

#[no_mangle]
pub fn curr_el_sp0_serror_el1(ctx: *mut AllContext, _sp: usize, esr: usize) {
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

    wait_forever();
}

// from the current EL using the SP_EL1
#[no_mangle]
pub fn curr_el_spx_sync_el1(ctx: *mut AllContext, _sp: usize, esr: usize) {
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

    wait_forever();
}

#[no_mangle]
pub fn curr_el_spx_irq_el1(ctx: *mut AllContext, sp: usize, esr: usize) {
    let context = unsafe { &mut *ctx };

    // Log the context of the interrupt for debugging
    log::info!(
        "IRQ received at EL1:
        Stack pointer: 0x{:x}
        Exception Syndrome Register (ESR): 0x{:x}
        Return address: 0x{:x}",
        sp,
        esr,
        context.elr
    );

    if awkernel_aarch64::spsel::get() & 1 == 0 {
        log::info!("Use SP_EL0.");
    } else {
        log::info!("Use SP_ELx.");
    }

    wait_forever();
}

#[no_mangle]
pub fn curr_el_spx_fiq_el1(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn curr_el_spx_serror_el1(ctx: *mut AllContext, _sp: usize, esr: usize) {
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

    wait_forever();
}

// from lower EL (AArch64)
#[no_mangle]
pub fn lower_el_aarch64_sync_el1(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch64_irq_el1(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch64_fiq_el1(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch64_serror_el1(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

// from lower EL (AArch32)
#[no_mangle]
pub fn lower_el_aarch32_sync_el1(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch32_irq_el1(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch32_fiq_el1(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}

#[no_mangle]
pub fn lower_el_aarch32_serror_el1(_ctx: *mut AllContext, _sp: usize, _esr: usize) {}
