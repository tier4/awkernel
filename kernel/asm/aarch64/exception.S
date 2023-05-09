.macro CALL_WITH_CONTEXT handler elr_reg spsr_reg
    // Store x0 and x1 on the stack.
    stp     x0, x1, [sp, #16 * -17]
    stp     x2, x3, [sp, #16 * -16]

    // Store x30 and the exception link register.
    mrs     x1, \elr_reg
    stp     lr, x1, [sp, #16 * -2]

    // Store SPSR.
    mrs     x2, \spsr_reg
    str     w2, [sp, #16 * -1] // Context::spsr

    bl      exception_store_registers

    // x0 is the first argument for the function called through `\handler`.
    mov     x0, sp

    // x1 is the second argument for the function called through `\handler`.
    add     x1, sp, #16 * 50

    // Call `\handler`.
    bl      \handler

    mov     x28, sp

    add     x0, sp, #16 * 48
    ldp     lr, x1, [x0], #16 // x30 and ELR.
    ldr     x2, [x0] // SPSR

    add     sp, sp, #16 * 50 // Restore SP.

    msr     \elr_reg,  x1 // Restore ELR.
    msr     \spsr_reg, x2 // Restore SPSR.

    // After returning from exception handling code, replay the saved context and return via `eret`.
    b       exception_restore_context
.endm

exception_store_registers:
    // Store general purpose registers.
    stp      x4,  x5, [sp, #16 * -15]
    stp      x6,  x7, [sp, #16 * -14]
    stp      x8,  x9, [sp, #16 * -13]
    stp     x10, x11, [sp, #16 * -12]
    stp     x12, x13, [sp, #16 * -11]
    stp     x14, x15, [sp, #16 * -10]
    stp     x16, x17, [sp, #16 *  -9]
    stp     x18, x19, [sp, #16 *  -8]
    stp     x20, x21, [sp, #16 *  -7]
    stp     x22, x23, [sp, #16 *  -6]
    stp     x24, x25, [sp, #16 *  -5]
    stp     x26, x27, [sp, #16 *  -4]
    stp     x28, x29, [sp, #16 *  -3]

    // Store SP.
    mov     x0, sp
    str     x0, [sp, -8] // Context::sp

    // Make room on the stack for the exception context.
    sub     sp, sp, #16 * 50 // size of Context

    mov     x0, sp // Context::fp_regs

    // Store all floating-point registers.
    str      q0, [x0], #16
    str      q1, [x0], #16
    str      q2, [x0], #16
    str      q3, [x0], #16
    str      q4, [x0], #16
    str      q5, [x0], #16
    str      q6, [x0], #16
    str      q7, [x0], #16
    str      q8, [x0], #16
    str      q9, [x0], #16
    str     q10, [x0], #16
    str     q11, [x0], #16
    str     q12, [x0], #16
    str     q13, [x0], #16
    str     q14, [x0], #16
    str     q15, [x0], #16
    str     q16, [x0], #16
    str     q17, [x0], #16
    str     q18, [x0], #16
    str     q19, [x0], #16
    str     q20, [x0], #16
    str     q21, [x0], #16
    str     q22, [x0], #16
    str     q23, [x0], #16
    str     q24, [x0], #16
    str     q25, [x0], #16
    str     q26, [x0], #16
    str     q27, [x0], #16
    str     q28, [x0], #16
    str     q29, [x0], #16
    str     q30, [x0], #16
    str     q31, [x0], #16

    // Store FPSR and FPCR registers.
    mrs     x3, fpsr
    mrs     x4, fpcr

    stp     x3, x4, [x0]

    ret

//--------------------------------------------------------------------------------------------------
// Helper functions
//--------------------------------------------------------------------------------------------------
exception_restore_context:
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

    eret

sync_el1:
    CALL_WITH_CONTEXT lower_el_aarch64_sync_el1 ELR_EL1 SPSR_EL1

#if defined(raspi3) || defined(raspi4)
    .balign 0x800
exception_vector_el2:
    // from the current EL using SP0
    CALL_WITH_CONTEXT curr_el_sp0_sync_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_irq_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_fiq_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_serror_el2 ELR_EL2 SPSR_EL2

    // from the current EL using the current SP
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_sync_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_irq_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_fiq_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_serror_el2 ELR_EL2 SPSR_EL2

    // from lower EL (AArch64)
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_sync_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_irq_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_fiq_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_serror_el2 ELR_EL2 SPSR_EL2

    // from lower EL (AArch32)
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_sync_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_irq_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_fiq_el2 ELR_EL2 SPSR_EL2
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_serror_el2 ELR_EL2 SPSR_EL2
#endif // defined(raspi3) || defined(raspi4)

    .balign 0x800
exception_vector_el1:
    // from the current EL using SP0
    CALL_WITH_CONTEXT curr_el_sp0_sync_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_irq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_fiq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_serror_el1 ELR_EL1 SPSR_EL1

    // from the current EL using the current SP
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_sync_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_irq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_fiq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_spx_serror_el1 ELR_EL1 SPSR_EL1

    // from lower EL (AArch64)
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_irq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_fiq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch64_serror_el1 ELR_EL1 SPSR_EL1

    // from lower EL (AArch32)
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_sync_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_irq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_fiq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    CALL_WITH_CONTEXT lower_el_aarch32_serror_el1 ELR_EL1 SPSR_EL1
