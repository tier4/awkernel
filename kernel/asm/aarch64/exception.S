.macro CALL_WITH_CONTEXT handler elr_reg spsr_reg
    // Make room on the stack for the exception context.
    sub     sp,  sp,  #16 * 17

    // Store all general purpose registers on the stack.
    stp     x0,  x1,  [sp, #16 * 0]
    stp     x2,  x3,  [sp, #16 * 1]
    stp     x4,  x5,  [sp, #16 * 2]
    stp     x6,  x7,  [sp, #16 * 3]
    stp     x8,  x9,  [sp, #16 * 4]
    stp     x10, x11, [sp, #16 * 5]
    stp     x12, x13, [sp, #16 * 6]
    stp     x14, x15, [sp, #16 * 7]
    stp     x16, x17, [sp, #16 * 8]
    stp     x18, x19, [sp, #16 * 9]
    stp     x20, x21, [sp, #16 * 10]
    stp     x22, x23, [sp, #16 * 11]
    stp     x24, x25, [sp, #16 * 12]
    stp     x26, x27, [sp, #16 * 13]
    stp     x28, x29, [sp, #16 * 14]

    // Add the exception link register and the saved program status.
    mrs     x1, \elr_reg
    mrs     x2, \spsr_reg

    stp     lr,  x1,  [sp, #16 * 15]
    str     w2,       [sp, #16 * 16]

    // x0 is the first argument for the function called through `\handler`.
    mov     x0,  sp

    // x1 is the second argument for the function called through `\handler`.
    add     x1, sp, #16 * 17

    // Call `\handler`.
    bl      \handler

    ldr     w19,      [sp, #16 * 16]
    ldp     lr,  x20, [sp, #16 * 15]

    msr     \spsr_reg, x19
    msr     \elr_reg,  x20

    // After returning from exception handling code, replay the saved context and return via `eret`.
    b       exception_restore_context
.endm

//--------------------------------------------------------------------------------------------------
// Helper functions
//--------------------------------------------------------------------------------------------------
exception_restore_context:
    ldp     x2,  x3,  [sp, #16 * 1]
    ldp     x4,  x5,  [sp, #16 * 2]
    ldp     x6,  x7,  [sp, #16 * 3]
    ldp     x8,  x9,  [sp, #16 * 4]
    ldp     x10, x11, [sp, #16 * 5]
    ldp     x12, x13, [sp, #16 * 6]
    ldp     x14, x15, [sp, #16 * 7]
    ldp     x16, x17, [sp, #16 * 8]
    ldp     x18, x19, [sp, #16 * 9]
    ldp     x20, x21, [sp, #16 * 10]
    ldp     x22, x23, [sp, #16 * 11]
    ldp     x24, x25, [sp, #16 * 12]
    ldp     x26, x27, [sp, #16 * 13]
    ldp     x28, x29, [sp, #16 * 14]

    mrs     x0, spsel
    cmp     x0, xzr
    b.eq    exception_restore_context_sp_el0
    b       exception_restore_context_sp_el1

exception_restore_context_sp_el0:
    ldp     x0,  x1,  [sp, #16 * 0]
    add     sp,  sp,  #16 * 17

    eret

exception_restore_context_sp_el1:
    // restore interrupt mask
    ldr     x0, [sp, #16 * 17]
    msr     daif, x0

    ldp     x0,  x1,  [sp, #16 * 0]
    add     sp,  sp,  #16 * 18

    eret

sync_el1:
    CALL_WITH_CONTEXT lower_el_aarch64_sync_el1 ELR_EL1 SPSR_EL1

#if defined(raspi3) || defined(raspi4)
    .balign 0x800
exception_vector_el2:
    // from the current EL using the current SP0
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
    // from the current EL using the current SP0
    CALL_WITH_CONTEXT curr_el_sp0_sync_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    msr     spsel, #0 // Select SP_EL0
    CALL_WITH_CONTEXT curr_el_sp0_irq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    msr     spsel, #0 // Select SP_EL0
    CALL_WITH_CONTEXT curr_el_sp0_fiq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    msr     spsel, #0 // Select SP_EL0
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
    sub     sp, sp, #16 * 2
    stp     x0, x1, [sp, #16 * 0]

    mrs     x0, daif
    mrs     x18, esr_el1
    str     x0, [sp, #16 * 1]
    msr     daifset, 0b11 // mask IRQ and FIQ

    // check DATA abort
    lsr     x0, x18, #27
    and     x0, x0, #0b11111
    cmp     x0, #0b10010
    b.eq    1f

    // SP_EL0

    // restore interrupt mask
    ldr     x0, [sp, #16 * 1]
    msr     daif, x0

    ldp     x0, x1, [sp, #16 * 0]
    add     sp, sp, #16 * 2

    msr     spsel, #0 // Select SP_EL0

    b       sync_el1
1:
    // SP_EL1
    ldp     x0, x1, [sp, #16 * 0]
    add     sp, sp, #16 * 1

    b       sync_el1

    .balign 0x80
    msr     spsel, #0 // Select SP_EL0
    CALL_WITH_CONTEXT lower_el_aarch64_irq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    msr     spsel, #0 // Select SP_EL0
    CALL_WITH_CONTEXT lower_el_aarch64_fiq_el1 ELR_EL1 SPSR_EL1
    .balign 0x80
    msr     spsel, #0 // Select SP_EL0
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
