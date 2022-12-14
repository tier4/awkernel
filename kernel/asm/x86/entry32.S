.section .text
.global _entry32

#define CR0_PG_MASK 0x1fffffff
#define CR0_PG (1 << 31)
#define CR4_PAE (1 << 5)

#define EFER_MSR 0xc0000080
#define EFER_LME (1 << 8)  // long mode enable
#define EFER_LMA (1 << 10) // long mode active
#define EFER_NXE (1 << 11) // No-execute enable

#define CPU0_GDTR (1024 * 6)
#define CPU0_CR3 (1024 * 6 + 8)

#define STACK_START (256 * 1024 * 1024)
#define STACK_SIZE (2 * 1024 * 1024)

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

    // Enable long mode.
    movl    $EFER_MSR, %ecx
    rdmsr
    orl     $(EFER_LME | EFER_LMA | EFER_NXE), %eax
    wrmsr

    // Enable paging.
    movl    %cr0, %eax
    orl     $CR0_PG, %eax
    movl    %eax, %cr0

    // Get local APIC ID.
    movl    $1, %eax
    cpuid
    shrl    $24, %ebx // 31:24 is local APIC ID
    andl    $0xFF, %ebx

    // Set stack pointer.
    movl    %ebx, %eax
    movl    $STACK_SIZE, %ecx
    mull    %ecx
    addl    $STACK_START, %ecx
    movl    %ecx, %esp
    movl    %ecx, %ebp

    pushl   $(1 << 3)
    pushl   $entry64

    // Set GDTR up.
    // movl    $CPU0_GDTR, %eax
    // movl    (%eax), %ebx
    // lgdt    (%ebx)

    lret

.code64  # Tell assembler to generate 64-bit code now.
entry64:

loop:
    hlt
    jmp     loop
