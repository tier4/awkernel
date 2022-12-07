.section .text, "x"
.global _start_cpu

// Address of _start_cpu
#define ADDR_OFFSET 0x1000

_start_cpu:
    // Disable interrupts
    cli

    // Calculate the base address
    movl    $ADDR_OFFSET, %eax
    movw    %ax, %ds

    // Initialize IDT and GDT
    lidt    %ds:(idtr - _start_cpu)
    lgdt    %ds:(gdtr - _start_cpu)

    // Entering the protected mode
    movl    %cr0, %eax
    orl     $0x1, %eax
    movl    %eax, %cr0
    // ljmpl	$AP_GDT_CODE32_SEL,$(ap_entry32 - KERNEL_RELOCBASE)

    .align  16

/* Pseudo interrupt descriptor table */
idtr:
    .word   0x0		/* Limit */
    .long   0x0		/* Base address */
/* Temporary global descriptor table */
gdt:
    .word	0x0,0x0,0x0,0x0		/* Null descriptor */
    .word	0xffff,0x0,0x9a00,0xaf	/* Code 64 */
    .word	0xffff,0x0,0x9200,0xaf	/* Data 64 */
    .word	0xffff,0x0,0x9a00,0xcf	/* Code 32 */
    .word	0xffff,0x0,0x9200,0xcf	/* Data 32 */
    .word	0xffff,0x0,0x9a00,0x8f	/* Code 16 */
    .word	0xffff,0x0,0x9200,0x8f	/* Data 16 */
gdt.1:
gdtr:
    .word	gdt.1 - gdt - 1	/* Limit */
    .long	gdt		/* Base address */
