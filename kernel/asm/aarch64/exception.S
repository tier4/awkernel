.macro CALL_WITH_CONTEXT handler el spsr_reg
    // disable all interrupt
    msr     DAIFSet, #0x0f

    // handle data abort
    mrs     x18, esr_\el
    lsr     x18, x18, #27
    and     x18, x18, #0b11111

    eor     x18, x18, #0b10000 // x18 == 0b10010 ?
    eor     x18, x18, #0b00010

    cbz     x18, data_abort

    // Store x0 - x3 on the stack.
    stp     x0, x1, [sp, #16 * -17]
    stp     x2, x3, [sp, #16 * -16]

    // Store x31 and ELR.
    mrs     x3, elr_\el
    stp     lr, x3, [sp, #16 * -2]

    // x2 is the third argument for the function called through `\handler`.
    mrs     x2, esr_\el

    // Store SPSR.
    mrs     x3, \spsr_reg
    str     w3, [sp, #16 * -1] // Context::spsr

    // Make room on the stack for the exception context.
    sub     sp, sp, #16 * 50 // size of Context

    // enable all interrupt
    msr     DAIFClr, #0x0f

    // x1 is the second argument for the function called through `\handler`.
    add     x1, sp, #16 * 50 // SP (original)

    bl      exception_store_registers

    // x0 is the first argument for the function called through `\handler`.
    mov     x0, sp // Context

    // Call `\handler`.
    bl      \handler

    add     x0, sp, #16 * 48
    ldp     lr, x1, [x0], #16 // x30 and ELR.
    ldr     x2, [x0] // SPSR

    msr     elr_\el,  x1 // Restore ELR.
    msr     \spsr_reg, x2 // Restore SPSR.

    // After returning from exception handling code, replay the saved context and return via `eret`.
    b       exception_restore_context
.endm

// TODO
data_abort:
1:
    wfi
    b       1b

//--------------------------------------------------------------------------------------------------
// Helper functions
//--------------------------------------------------------------------------------------------------
exception_store_registers:
    // Store SP.
    str     x1, [x1, -8] // Context::sp

    // Store general purpose registers.
    stp      x4,  x5, [x1, #16 * -15]
    stp      x6,  x7, [x1, #16 * -14]
    stp      x8,  x9, [x1, #16 * -13]
    stp     x10, x11, [x1, #16 * -12]
    stp     x12, x13, [x1, #16 * -11]
    stp     x14, x15, [x1, #16 * -10]
    stp     x16, x17, [x1, #16 *  -9]
    stp     x18, x19, [x1, #16 *  -8]
    stp     x20, x21, [x1, #16 *  -7]
    stp     x22, x23, [x1, #16 *  -6]
    stp     x24, x25, [x1, #16 *  -5]
    stp     x26, x27, [x1, #16 *  -4]
    stp     x28, x29, [x1, #16 *  -3]

    mov     x3, sp // Context::fp_regs

    // Store all floating-point registers.
    str      q0, [x3], #16
    str      q1, [x3], #16
    str      q2, [x3], #16
    str      q3, [x3], #16
    str      q4, [x3], #16
    str      q5, [x3], #16
    str      q6, [x3], #16
    str      q7, [x3], #16
    str      q8, [x3], #16
    str      q9, [x3], #16
    str     q10, [x3], #16
    str     q11, [x3], #16
    str     q12, [x3], #16
    str     q13, [x3], #16
    str     q14, [x3], #16
    str     q15, [x3], #16
    str     q16, [x3], #16
    str     q17, [x3], #16
    str     q18, [x3], #16
    str     q19, [x3], #16
    str     q20, [x3], #16
    str     q21, [x3], #16
    str     q22, [x3], #16
    str     q23, [x3], #16
    str     q24, [x3], #16
    str     q25, [x3], #16
    str     q26, [x3], #16
    str     q27, [x3], #16
    str     q28, [x3], #16
    str     q29, [x3], #16
    str     q30, [x3], #16
    str     q31, [x3], #16

    // Store FPSR and FPCR registers.
    mrs     x0, fpsr
    mrs     x4, fpcr
    stp     x0, x4, [x3]

    ret

exception_restore_context:
    mov     x28, sp

    ldr      q0, [x28], #16
    ldr      q1, [x28], #16
    ldr      q2, [x28], #16
    ldr      q3, [x28], #16
    ldr      q4, [x28], #16
    ldr      q5, [x28], #16
    ldr      q6, [x28], #16
    ldr      q7, [x28], #16
    ldr      q8, [x28], #16
    ldr      q9, [x28], #16
    ldr     q10, [x28], #16
    ldr     q11, [x28], #16
    ldr     q12, [x28], #16
    ldr     q13, [x28], #16
    ldr     q14, [x28], #16
    ldr     q15, [x28], #16
    ldr     q16, [x28], #16
    ldr     q17, [x28], #16
    ldr     q18, [x28], #16
    ldr     q19, [x28], #16
    ldr     q20, [x28], #16
    ldr     q21, [x28], #16
    ldr     q22, [x28], #16
    ldr     q23, [x28], #16
    ldr     q24, [x28], #16
    ldr     q25, [x28], #16
    ldr     q26, [x28], #16
    ldr     q27, [x28], #16
    ldr     q28, [x28], #16
    ldr     q29, [x28], #16
    ldr     q30, [x28], #16
    ldr     q31, [x28], #16

    ldp     x0, x1, [x28], #16 // Load FPSR and FPCR.

    msr     fpsr, x0 // Restore FPSR
    msr     fpcr, x1 // Restore FPCR.

    ldp      x0,  x1, [x28], #16
    ldp      x2,  x3, [x28], #16
    ldp      x4,  x5, [x28], #16
    ldp      x6,  x7, [x28], #16
    ldp      x8,  x9, [x28], #16
    ldp     x10, x11, [x28], #16
    ldp     x12, x13, [x28], #16
    ldp     x14, x15, [x28], #16
    ldp     x16, x17, [x28], #16
    ldp     x18, x19, [x28], #16
    ldp     x20, x21, [x28], #16
    ldp     x22, x23, [x28], #16
    ldp     x24, x25, [x28], #16
    ldp     x26, x27, [x28], #16
    ldp     x28, x29, [x28]

    add     sp, sp, #16 * 50 // Restore SP.

    eret

#if defined(raspi3) || defined(raspi4)
    .balign 0x800
exception_vector_el2:
    // from the current EL using SP0
    CALL_WITH_CONTEXT curr_el_sp0_sync_el2 el2 spsr_el2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_irq_el2 el2 spsr_el2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_fiq_el2 el2 spsr_el2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_serror_el2 el2 spsr_el2

    // from the current EL using the current SP
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_sync_el2 el2 spsr_el2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_irq_el2 el2 spsr_el2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_fiq_el2 el2 spsr_el2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_serror_el2 el2 spsr_el2

    // from lower EL (AArch64)
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_sync_el2 el2 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_irq_el2 el2 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_fiq_el2 el2 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_serror_el2 el2 spsr_el1

    // from lower EL (AArch32)
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_sync_el2 el2 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_irq_el2 el2 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_fiq_el2 el2 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_serror_el2 el2 spsr_el1
#endif // defined(raspi3) || defined(raspi4)

    .balign 0x800
exception_vector_el1:
    // from the current EL using SP0
    CALL_WITH_CONTEXT curr_el_sp0_sync_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_irq_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_fiq_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_serror_el1 el1 spsr_el1

    // from the current EL using the current SP
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_sync_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_irq_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_fiq_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_serror_el1 el1 spsr_el1

    // from lower EL (AArch64)
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_sync_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_irq_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_fiq_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_serror_el1 el1 spsr_el1

    // from lower EL (AArch32)
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_sync_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_irq_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_fiq_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_serror_el1 el1 spsr_el1
