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

    // Set segment registers.
    movl    $(1 << 3), %eax
    movl    $(2 << 3), %ebx
    movw    %ax, %cs
    movw    %bx, %ss
    movw    %bx, %ds
    movw    %bx, %es
    movw    %bx, %fs
    movw    %bx, %gs

    // Entering the protected mode
    movl    %cr0, %eax
    orl     $0x1, %eax
    movl    %eax, %cr0
    // ljmpl	$AP_GDT_CODE32_SEL,$(ap_entry32 - KERNEL_RELOCBASE)

loop:
    movl    [(ADDR_OFFSET + 1024)], %eax
    addl    $1, %eax
    movl    %eax, [(ADDR_OFFSET + 1024)]
    hlt
    jmp     (loop + ADDR_OFFSET)

    .align  16

/* Pseudo interrupt descriptor table */
idtr:
    .word   0x0		/* Limit */
    .long   0x0		/* Base address */
/* Temporary global descriptor table */
gdt:
    .long   0x0, 0x0    // NULL descriptor

    // Execute/Read Segment
    .word   0xffff      // Segment Limit 15:00
    .word   0           // Base Address  15:00
    .byte   0           // Base Address  23:16

    // P    (1 bit) : segment Present
    // DPL  (2 bits): Descriptor Priviledged Level field. 0 to 3, with 0 being the most priviledged level
    // S    (1 bit) : descriptor type flag. 0 indicates a system segment, and 1 indicates a code or data segment
    // Type (4 bits): segment type
    .byte   (1 << 7) /* P */ | (1 << 4) /* S */ | 0x0a // Execute/Read

    // G   (1 bit): granuality flag. Determines the scaling of the segment limit field.
    //              0 indicates the segment limit is interpreted in byte units
    //              1 indicates it is interpreted in byte units 4KiB units
    // D/B (1 bit): default operation size/default stack pointer size and/or upper bound flag
    //              This shoud always be set to 1 for 32-bit code and data segments
    // L   (1 bit): 64-bit code segment flag
    // AVL (1 bit): AVailabLe and reserved bits. available for use by system software.
    // Segment Limit 19:16 (4 bits)
    .byte   (1 << 7) /* G */ | (1 << 6) /* D/B */ | 0x0F /* Seg. Limit 19:16 */

    .byte   0       // Base Address 31:24

    // Read/Write Segment
    .word   0xffff      // Segment Limit 15:00
    .word   0           // Base Address  15:00
    .byte   0           // Base Address  23:16

    // P    (1 bit) : segment Present
    // DPL  (2 bits): Descriptor Priviledged Level field. 0 to 3, with 0 being the most priviledged level
    // S    (1 bit) : descriptor type flag. 0 indicates a system segment, and 1 indicates a code or data segment
    // Type (4 bits): segment type
    .byte   (1 << 7) /* P */ | (1 << 4) /* S */ | 0x02 // Read/Write

    // G   (1 bit): granuality flag. Determines the scaling of the segment limit field.
    //              0 indicates the segment limit is interpreted in byte units
    //              1 indicates it is interpreted in byte units 4KiB units
    // D/B (1 bit): default operation size/default stack pointer size and/or upper bound flag
    //              This shoud always be set to 1 for 32-bit code and data segments
    // L   (1 bit): 64-bit code segment flag
    // AVL (1 bit): AVailabLe and reserved bits. available for use by system software.
    // Segment Limit 19:16 (4 bits)
    .byte   (1 << 7) /* G */ | (1 << 6) /* D/B */ | 0x0F /* Seg. Limit 19:16 */

    .byte   0       // Base Address 31:24

gdt.1:
gdtr:
    .word	gdt.1 - gdt - 1	// size of GDT - 1
    .long	gdt             // Base address
