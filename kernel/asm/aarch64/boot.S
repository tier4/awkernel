#if defined(raspi3) || defined(raspi4)
    #include "device/raspi.S"
#endif

#define CPUECTLR_EL1        S3_1_C15_C2_1
#define CPUECTLR_EL1_SMPEN  (1 << 6);

#define L2CTLR_EL1          S3_1_C11_C0_2

#define SCR_RW              (1 << 10)
#define SCR_HCE             (1 << 8)  // Enable hypervisor call
#define SCR_SMD             (1 << 7)  // Disable secure monitor call
#define SCR_RES1_5          (1 << 5)
#define SCR_RES1_4          (1 << 4)
#define SCR_NS              (1 << 0)  // EL0 and EL1 are non-secure world

#define SCR_VAL (SCR_RW | SCR_SMD | SCR_RES1_5 | SCR_RES1_4 | SCR_NS)

boot_entry:
    /* Set SMPEN */
    mov     x0, #CPUECTLR_EL1_SMPEN
    msr     CPUECTLR_EL1, x0

    /* Set L2 read/write cache latency to 3 */
    mrs     x0, L2CTLR_EL1
    mov     x1, #0x22
    orr     x0, x0, x1
    msr     L2CTLR_EL1, x0

    // disable all interrupt (daif at bits 9..6)
    msr     DAIFSet, #0x0f

#ifdef GICv2
    bl      setup_gicv2
#endif

    // set stack before _start
    ldr     x1, =__stack_el1_start
    mrs     x2, mpidr_el1 // read cpu id
    and     x2, x2, #0xFF
    mov     x4, #(STACKSIZE)
    mul     x3, x2, x4
    sub     x1, x1, x3
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
    msr     sp_el0, x10  // set stack pointer
    msr     sp_el1, x10
    msr     spsel, #0

    mrs     x0, hcr_el2
    orr     x0, x0, #(1 << 31) // AArch64
    orr     x0, x0, #(1 << 1)  // SWIO hardwired on Pi3
    msr     hcr_el2, x0
    mrs     x0, hcr_el2

    // enable CNTP for EL1
    mrs     x1, cnthctl_el2
    orr     x1, x1, #3
    msr     cnthctl_el2, x1
    msr     cntvoff_el2, xzr

    ldr     x1, =exception_vector_el2
    msr     vbar_el2, x1

    /*
     * Set up sctlr_el2
     * All set bits below are res1. LE, no WXN/I/SA/C/A/M
     */
    ldr     x0, =0x30c50830
    msr     sctlr_el2, x0

    // get current EL
    mrs     x0, CurrentEL
    and     x0, x0, #(0b1100) // clear reserved bits

    // running at EL3?
    cmp     x0, #(3 << 2)
    beq     .EL3

    // running at EL2?
    cmp     x0, #(2 << 2)
    beq     .EL2

.EL3:
    ldr     x0, =SCR_VAL
    msr     SCR_EL3, x0

    /* Set up CNTFRQ_EL0 */
    ldr     x0, =OSC_FREQ
    msr     CNTFRQ_EL0, x0

    mov     x0, #0x33ff
    msr     cptr_el3, x0 // Disable coprocessor traps to EL3

    mov     x1, #0b100   // EL1t
    msr     spsr_el3, x1
    adr     x1, .EL1     // set entry point
    msr     elr_el3, x1

    eret

.EL2:
    // disable all interrupt (daif at bits 9..6)
    msr     DAIFSet, #0x0f

    // change execution level to EL1
    mov     x1, #0b100   // EL1t
    msr     spsr_el2, x1
    adr     x1, .EL1      // set entry point
    msr     elr_el2, x1

    eret

    // EL1t
.EL1:
    // disable all interrupt (daif at bits 9..6)
    msr     DAIFSet, #0x0f

    // set exception vector
    ldr     x1, =exception_vector_el1
    msr     vbar_el1, x1

    mov     sp, x10
    bl      kernel_main

.loop:
    wfe
    b       .loop

#ifdef GICv2

#define GICC_CTRLR          0x0
#define GICC_PMR            0x4
#define IT_NR               0x8 // Number of interrupt enable registers (256 total irqs)
#define GICD_CTRLR          0x0
#define GICD_IGROUPR        0x80

// Called from secure mode - set all interrupts to group 1 and enable.
setup_gicv2:
    mrs     x0, MPIDR_EL1
    ldr     x2, =GIC_DISTB
    tst     x0, #0x3
    b.eq    1f // primary core

    mov     w0, #3 // Enable group 0 and 1 IRQs from distributor
    str     w0, [x2, #GICD_CTRLR]
1:
    add     x1, x2, #(GIC_CPUB - GIC_DISTB)
    mov     w0, #0x1e7
    str     w0, [x1, #GICC_CTRLR] // Enable group 1 IRQs from CPU interface
    mov     w0, #0xff
    str     w0, [x1, #GICC_PMR] // priority mask
    add     x2, x2, #GICD_IGROUPR
    mov     x0, #(IT_NR * 4)
    mov     w1, #~0 // group 1 all the things
2:
    subs    x0, x0, #4
    str     w1, [x2, x0]
    b.ne    2b
    ret

#endif // GICv2

#include "exception.S"
