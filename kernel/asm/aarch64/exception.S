.macro CALL_WITH_CONTEXT handler elr_reg spsr_reg
    // Make room on the stack for the exception context.
    sub     sp,  sp,  #16 * 50

    // Store x0 - x3 on the stack.
    stp     x0,  x1, [sp, #16 *  0]
    stp     x2,  x3, [sp, #16 *  1]
    stp     x4,  x5, [sp, #16 *  2]

    // Store the exception link register and the saved program status.
    mrs     x1, \elr_reg
    mrs     x2, \spsr_reg

    add     x0, sp, #16 * 15
    stp     lr, x1, [x0, #16 * 0]
    stp     w2, w3, [x0, #16 * 1]

    // Store FPSR and FPCR registers.
    mrs     x3, fpsr
    mrs     x4, fpcr

    add     x0, sp, #16 * 49
    stp     x3, x4, [x0]

    bl      store_registers

    // x0 is the first argument for the function called through `\handler`.
    mov     x0,  sp

    // x1 is the second argument for the function called through `\handler`.
    add     x1, sp, #16 * 50

    // Call `\handler`.
    bl      \handler

    mov     x4, sp           // Stack pointer.
    add     x5, sp, #16 * 15 // Address to x30.
    add     x6, sp, #16 * 17 // Address to floating-point regsiters.
    add     x0, sp, #16 * 49 // Address to FPSR.
    add     sp, sp, #16 * 50 // Restore the stack pointer.

    ldp     lr, x1, [x5, #16 * 0] // Restore x30 and load ELR.
    ldr     w2, [x5, #16 * 1] // Load SPSR.

    msr     \elr_reg,  x1 // Restore ELR
    msr     \spsr_reg, x2 // Restore SPSR.

    ldp     x1, x2, [x0] // Load FPSR and FPCR.

    msr     fpsr, x1 // Restore FPSR
    msr     fpcr, x2 // Restore FPCR.

    // After returning from exception handling code, replay the saved context and return via `eret`.
    b       exception_restore_context
.endm

store_registers:
    // Store general purpose registers.
    stp      x6,  x7, [sp, #16 *  3]
    stp      x8,  x9, [sp, #16 *  4]
    stp     x10, x11, [sp, #16 *  5]
    stp     x12, x13, [sp, #16 *  6]
    stp     x14, x15, [sp, #16 *  7]
    stp     x16, x17, [sp, #16 *  8]
    stp     x18, x19, [sp, #16 *  9]
    stp     x20, x21, [sp, #16 * 10]
    stp     x22, x23, [sp, #16 * 11]
    stp     x24, x25, [sp, #16 * 12]
    stp     x26, x27, [sp, #16 * 13]
    stp     x28, x29, [sp, #16 * 14]

    add     x0, sp, #16 * 17

    // Store all floating-point registers.
    str      q0, [x0], #32
    str      q1, [x0], #32
    str      q2, [x0], #32
    str      q3, [x0], #32
    str      q4, [x0], #32
    str      q5, [x0], #32
    str      q6, [x0], #32
    str      q7, [x0], #32
    str      q8, [x0], #32
    str      q9, [x0], #32
    str     q10, [x0], #32
    str     q11, [x0], #32
    str     q12, [x0], #32
    str     q13, [x0], #32
    str     q14, [x0], #32
    str     q15, [x0], #32
    str     q16, [x0], #32
    str     q17, [x0], #32
    str     q18, [x0], #32
    str     q19, [x0], #32
    str     q20, [x0], #32
    str     q21, [x0], #32
    str     q22, [x0], #32
    str     q23, [x0], #32
    str     q24, [x0], #32
    str     q25, [x0], #32
    str     q26, [x0], #32
    str     q27, [x0], #32
    str     q28, [x0], #32
    str     q29, [x0], #32
    str     q30, [x0], #32
    str     q31, [x0]
    ret

//--------------------------------------------------------------------------------------------------
// Helper functions
//--------------------------------------------------------------------------------------------------
exception_restore_context:
    ldr      q0, [x6], #32
    ldr      q1, [x6], #32
    ldr      q2, [x6], #32
    ldr      q3, [x6], #32
    ldr      q4, [x6], #32
    ldr      q5, [x6], #32
    ldr      q6, [x6], #32
    ldr      q7, [x6], #32
    ldr      q8, [x6], #32
    ldr      q9, [x6], #32
    ldr     q10, [x6], #32
    ldr     q11, [x6], #32
    ldr     q12, [x6], #32
    ldr     q13, [x6], #32
    ldr     q14, [x6], #32
    ldr     q15, [x6], #32
    ldr     q16, [x6], #32
    ldr     q17, [x6], #32
    ldr     q18, [x6], #32
    ldr     q19, [x6], #32
    ldr     q20, [x6], #32
    ldr     q21, [x6], #32
    ldr     q22, [x6], #32
    ldr     q23, [x6], #32
    ldr     q24, [x6], #32
    ldr     q25, [x6], #32
    ldr     q26, [x6], #32
    ldr     q27, [x6], #32
    ldr     q28, [x6], #32
    ldr     q29, [x6], #32
    ldr     q30, [x6], #32
    ldr     q31, [x6]

    ldp      x0,  x1, [x4, #16 *  0]
    ldp      x2,  x3, [x4, #16 *  1]
    ldp      x4,  x5, [x4, #16 *  2]
    ldp      x6,  x7, [x4, #16 *  3]
    ldp      x8,  x9, [x4, #16 *  4]
    ldp     x10, x11, [x4, #16 *  5]
    ldp     x12, x13, [x4, #16 *  6]
    ldp     x14, x15, [x4, #16 *  7]
    ldp     x16, x17, [x4, #16 *  8]
    ldp     x18, x19, [x4, #16 *  9]
    ldp     x20, x21, [x4, #16 * 10]
    ldp     x22, x23, [x4, #16 * 11]
    ldp     x24, x25, [x4, #16 * 12]
    ldp     x26, x27, [x4, #16 * 13]
    ldp     x28, x29, [x4, #16 * 14]

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
