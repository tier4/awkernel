.section .text
.global _entry32

#define CR0_PG_MASK 0x7fffffff
#define CR4_PAE (1 << 5)

#define CPU0_CR3 (1024 * 6)

.code32  # Tell assembler to generate 32-bit code now.
_entry32:
    // Disable i8259 PIC.
    movb    0xff, %al
    outb    $0xa1
    outb    $0x21

    // Clear the PG-bit of CR0.
    movl    %cr0, %eax
    andl    $CR0_PG_MASK, %eax
    movl    %eax, %cr0

    // Load CPU0's CR3.
    movl    $CPU0_CR3, %eax
    movl    (%eax), %ebx
    movl    %ebx, %cr3

    // Enable PAE on CR4.
    movl    %cr4, %eax
    orl     $CR4_PAE, %eax
    movl    %eax, %cr4

loop:
    hlt
    jmp     loop
