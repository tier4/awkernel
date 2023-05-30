// This file is specified by `specification/kernel/asm/aarch64/exception.S`.
// If you update this file, please update and the specification and verify.

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
    stp       q0,  q1, [x3], #32
    stp       q2,  q3, [x3], #32
    stp       q4,  q5, [x3], #32
    stp       q6,  q7, [x3], #32
    stp       q8,  q9, [x3], #32
    stp      q10, q11, [x3], #32
    stp      q12, q13, [x3], #32
    stp      q14, q15, [x3], #32
    stp      q16, q17, [x3], #32
    stp      q18, q19, [x3], #32
    stp      q20, q21, [x3], #32
    stp      q22, q23, [x3], #32
    stp      q24, q25, [x3], #32
    stp      q26, q27, [x3], #32
    stp      q28, q29, [x3], #32
    stp      q30, q31, [x3], #32

    // Store FPSR and FPCR registers.
    mrs     x0, fpsr
    mrs     x4, fpcr
    stp     x0, x4, [x3]

    ret

exception_restore_context:
    mov     x28, sp

    ldp       q0,  q1, [x28], #32
    ldp       q2,  q3, [x28], #32
    ldp       q4,  q5, [x28], #32
    ldp       q6,  q7, [x28], #32
    ldp       q8,  q9, [x28], #32
    ldp      q10, q11, [x28], #32
    ldp      q12, q13, [x28], #32
    ldp      q14, q15, [x28], #32
    ldp      q16, q17, [x28], #32
    ldp      q18, q19, [x28], #32
    ldp      q20, q21, [x28], #32
    ldp      q22, q23, [x28], #32
    ldp      q24, q25, [x28], #32
    ldp      q26, q27, [x28], #32
    ldp      q28, q29, [x28], #32
    ldp      q30, q31, [x28], #32

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

    // enable all interrupt
    msr     DAIFClr, #0x0f

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
