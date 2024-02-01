.section .init, "x"
.global _start

_start:
    // disable all interrupt (daif at bits 9..6)
    msr     DAIFSet, #0x0f

    // set stack before _start
    mrs     x2, mpidr_el1 // read cpu id
    and     x2, x2, #0xFF
    add     x3, x2, #1

    mov     x4, #(STACKSIZE)
    mul     x3, x3, x4

    ldr     x1, =__stack_memory
    add     x1, x1, x3
    mov     x10, x1 // save stack pointer

    cbnz    x2, 2f

    // if cpu id == 0

    // clear bss
    ldr     x1, =__bss_start
    ldr     w2, =__bss_size

1:
    cbz     w2, 2f
    str     xzr, [x1], #8
    sub     w2, w2, #1
    cbnz    w2, 1b

2:
    // get current EL
    mrs     x4, CurrentEL
    and     x5, x4, #(0b1100) // clear reserved bits
    cmp     x5, #(1 << 2)
    beq     .EL1

    mrs     x4, hcr_el2
    orr     x4, x4, #(1 << 31) // AArch64
    orr     x4, x4, #(1 << 1)  // SWIO hardwired
    msr     hcr_el2, x4

    // enable CNTP for EL1
    mrs     x1, cnthctl_el2
    orr     x1, x1, #3
    msr     cnthctl_el2, x1
    msr     cntvoff_el2, xzr

    ldr     x1, =exception_vector_el2
    msr     vbar_el2, x1

    msr     sp_el0, x10  // set stack pointer
    msr     sp_el1, x10

    // running at EL3?
    cmp     x5, #(3 << 2)
    beq     .EL3

    // running at EL2?
    cmp     x5, #(2 << 2)
    beq     .EL2

.EL3:
    b       .loop

.EL2:
    // change execution level to EL1
    mov     x1, #0b100   // EL1t
    msr     spsr_el2, x1
    adr     x1, .EL1     // set entry point
    msr     elr_el2, x1

    eret

    // EL1t
.EL1:
    // disable all interrupt (daif at bits 9..6)
    msr     DAIFSet, #0x0f
    msr     spsel, #0

    // set exception vector
    ldr     x1, =exception_vector_el1
    msr     vbar_el1, x1

    mov     sp, x10
    bl      kernel_main

.loop:
    wfe
    b       .loop

#include "exception.S"
