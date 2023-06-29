// This file is specified by `specification/kernel/asm/aarch64/exception.S`.
// If you update this file, please update and the specification and verify.

.macro DATA_ABORT el
    // handle data abort
    mrs     x18, esr_\el
    lsr     x18, x18, #27
    and     x18, x18, #0b11111

    eor     x18, x18, #0b10000 // x18 == 0b10010 ?
    eor     x18, x18, #0b00010

    cbz     x18, data_abort
.endm

.macro CALL_WITH_CONTEXT handler el spsr_reg
    // disable interrupt
    msr     DAIFSet, #0x02

    // Make room on the stack for the exception context.
    sub     sp, sp, #800

    // Store x0 - x3, x30, and ELR on the stack.
    stp     x0, x1, [sp]

    mrs     x1, elr_\el

    stp     x2, x3, [sp, #16]
    stp     x30, x1, [sp, #240]

    add     x0, sp, #32
    mrs     x2, esr_\el
    mrs     x3, \spsr_reg

    bl      exception_store_registers

    // x0 is the first argument of `\handler`.
    mov     x0, sp // Context

    // x1 is the second argument fo `\handler`.
    add     x1, sp, #800

    // Call `\handler`.
    bl      \handler

    add     x0, sp, #248
    ldp     x1, x2, [x0], #16 // ELR and ESR
    ldr     w3, [x0], #8 // SPSR

    msr     elr_\el, x1 // Restore ELR.
    msr     esr_\el, x2 // Restore ESR.
    msr     \spsr_reg, x3 // Restore SPSR.

    // After returning from exception handling code, replay the saved context and return via `eret`.
    b       exception_restore_context
.endm

data_abort:
    // set stack before _start
    ldr     x1, =__stack_data_abort_start
    mrs     x2, mpidr_el1 // read cpu id
    and     x2, x2, #0xFF
    mov     x4, #4096 // stack size
    mul     x3, x2, x4
    sub     x1, x1, x3
    mov     sp, x1

    bl      handle_data_abort
1:
    wfi
    b       1b

//--------------------------------------------------------------------------------------------------
// Helper functions
//--------------------------------------------------------------------------------------------------
exception_store_registers:
    // Store general purpose registers.
    stp      x4,  x5, [x0], #16
    stp      x6,  x7, [x0], #16
    stp      x8,  x9, [x0], #16
    stp     x10, x11, [x0], #16
    stp     x12, x13, [x0], #16
    stp     x14, x15, [x0], #16
    stp     x16, x17, [x0], #16
    stp     x18, x19, [x0], #16
    stp     x20, x21, [x0], #16
    stp     x22, x23, [x0], #16
    stp     x24, x25, [x0], #16
    stp     x26, x27, [x0], #16
    stp     x28, x29, [x0], #32

    // Store ESR and SPSR.
    str     x2, [x0], #8
    str     w3, [x0], #8

    // Store FPSR and FPCR.
    mrs     x4, fpsr
    mrs     x5, fpcr
    stp     x4, x5, [x0], #16

    // Store all floating-point registers.
    stp      q0,  q1, [x0], #32
    stp      q2,  q3, [x0], #32
    stp      q4,  q5, [x0], #32
    stp      q6,  q7, [x0], #32
    stp      q8,  q9, [x0], #32
    stp     q10, q11, [x0], #32
    stp     q12, q13, [x0], #32
    stp     q14, q15, [x0], #32
    stp     q16, q17, [x0], #32
    stp     q18, q19, [x0], #32
    stp     q20, q21, [x0], #32
    stp     q22, q23, [x0], #32
    stp     q24, q25, [x0], #32
    stp     q26, q27, [x0], #32
    stp     q28, q29, [x0], #32
    stp     q30, q31, [x0], #32

    ret

exception_restore_context:
    ldp     x1, x2, [x0], #16 // Load FPSR and FPCR.

    msr     fpsr, x1 // Restore FPSR
    msr     fpcr, x2 // Restore FPCR.

    ldp      q0,  q1, [x0], #32
    ldp      q2,  q3, [x0], #32
    ldp      q4,  q5, [x0], #32
    ldp      q6,  q7, [x0], #32
    ldp      q8,  q9, [x0], #32
    ldp     q10, q11, [x0], #32
    ldp     q12, q13, [x0], #32
    ldp     q14, q15, [x0], #32
    ldp     q16, q17, [x0], #32
    ldp     q18, q19, [x0], #32
    ldp     q20, q21, [x0], #32
    ldp     q22, q23, [x0], #32
    ldp     q24, q25, [x0], #32
    ldp     q26, q27, [x0], #32
    ldp     q28, q29, [x0], #32
    ldp     q30, q31, [x0]

    mov     x30, sp

    ldp      x0,  x1, [x30], #16
    ldp      x2,  x3, [x30], #16
    ldp      x4,  x5, [x30], #16
    ldp      x6,  x7, [x30], #16
    ldp      x8,  x9, [x30], #16
    ldp     x10, x11, [x30], #16
    ldp     x12, x13, [x30], #16
    ldp     x14, x15, [x30], #16
    ldp     x16, x17, [x30], #16
    ldp     x18, x19, [x30], #16
    ldp     x20, x21, [x30], #16
    ldp     x22, x23, [x30], #16
    ldp     x24, x25, [x30], #16
    ldp     x26, x27, [x30], #16
    ldp     x28, x29, [x30], #16
    ldr     x30, [x30]

    add     sp, sp, #800 // Restore SP.

    // enable interrupt
    msr     DAIFClr, #0x02
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
    DATA_ABORT el1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_irq_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_fiq_el1 el1 spsr_el1
    .balign 0x80
    CALL_WITH_CONTEXT curr_el_sp0_serror_el1 el1 spsr_el1

    // from the current EL using the current SP
    .balign 0x80
    DATA_ABORT el1
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
