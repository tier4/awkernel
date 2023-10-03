.section .text
.global _entry32

#define CR0_PG_MASK 0x1fffffff
#define CR0_CD (1 << 30) // Cache Disable
#define CR0_PG (1 << 31)

#define CR4_PAE (1 << 5) // Physical Address Extension
#define CR4_PGE (1 << 7) // Page Global Enabled

#define EFER_MSR 0xc0000080
#define EFER_LME (1 << 8)  // long mode enable
#define EFER_LMA (1 << 10) // long mode active
#define EFER_NXE (1 << 11) // No-execute enable

#define NON_PRIMARY_KERNEL_MAIN (1024 * 2)
#define CPU0_CR3 (1024 * 2 + 8)

#define STACK_START (256 * 1024 * 1024)
#define STACK_SIZE (2 * 1024 * 1024)

#define SEG_KCODE_64 3
#define SEG_KDATA_64 4

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

    // Enable PAE ang PGE on CR4.
    movl    %cr4, %eax
    orl     $(CR4_PAE | CR4_PGE), %eax
    movl    %eax, %cr4

    // Enable long mode.
    movl    $EFER_MSR, %ecx
    rdmsr
    orl     $EFER_LME, %eax
    wrmsr

    movb    $'B', %al
    movw    $0x3F8, %dx
    outb    %al, %dx

    // Get local APIC ID.
    movl    $1, %eax
    cpuid
    shrl    $24, %ebx // 31:24 is local APIC ID
    andl    $0xFF, %ebx

    // Set stack pointer.
    movl    %ebx, %eax
    addl    $1, %eax
    movl    $STACK_SIZE, %ecx
    mull    %ecx
    addl    $STACK_START, %eax
    movl    %eax, %esp
    movl    %eax, %ebp

    pushl   $(SEG_KCODE_64 << 3)

    // Enable paging.
    movl    %cr0, %eax
    orl     $CR0_PG, %eax
    movl    $(CR0_CD), %ebx
    notl    %ebx
    andl    %ebx, %eax
    movl    %eax, %cr0

    jmp     entry64

    // Jump to entry64
    // pushl   $(SEG_KCODE_64 << 3)
    // pushl   $entry64

    // lret

.code64  # Tell assembler to generate 64-bit code now.
entry64:
    movb    $'C', %al
    movw    $0x3F8, %dx
    outb    %al, %dx

    jmp     loop

    movq    $NON_PRIMARY_KERNEL_MAIN, %rbx
    movq    (%rbx), %rax
    jmp     *%rax

loop:
    hlt
    jmp     loop
