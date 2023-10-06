.section .text
.global _entry32

// 11 0011
// 1: Protected Mode Enable
// 2: Monitor co-processor
// 4: Extension type
// 5: Numeric error

#define CR0_PG_MASK 0x1fffffff

#define CR0_MP (1 <<  1) // Monitor co-processor
#define CR0_ET (1 <<  4) // Extension type
#define CR0_NE (1 <<  5) // Numeric error
#define CR0_WP (1 << 16) // Write protect
#define CR0_CD (1 << 30) // Cache Disable
#define CR0_PG (1 << 31) // Paging


// 110 0110 1000
// 3: Debugging Extensions
// 5: Physical Address Extension
// 6: Machine Check Exception
// 9: Operating system support for FXSAVE and FXRSTOR instructions
// 10: Operating System Support for Unmasked SIMD Floating-Point Exceptions

#define CR4_DE  (1 << 3) // Debugging Extensions
#define CR4_PAE (1 << 5) // Physical Address Extension
#define CR4_MCE (1 << 6) // Machine Check Exception
#define CR4_PGE (1 << 7) // Page Global Enabled
#define CR4_OSFXSR (1 << 9) // Operating system support for FXSAVE and FXRSTOR instructions
#define CR4_OSXMMEXCPT (1 << 10) // Operating System Support for Unmasked SIMD Floating-Point Exceptions


// 1101 0000 0000

#define EFER_MSR 0xc0000080
#define EFER_LME (1 << 8)  // long mode enable
#define EFER_LMA (1 << 10) // long mode active
#define EFER_NXE (1 << 11) // No-execute enable

#define NON_PRIMARY_KERNEL_MAIN (1024 * 2)
#define CPU0_CR3  (1024 * 2 +  8)
#define CPU0_GDTR (CPU0_CR3 + 14)

#define SEG_KCODE_64 1
#define SEG_KDATA_64 2

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
    orl     $(CR4_DE | CR4_PAE | CR4_MCE | CR4_OSFXSR | CR4_OSXMMEXCPT), %eax
    movl    %eax, %cr4

spin:
    jmp     spin

    // Enable long mode.
    movl    $EFER_MSR, %ecx
    rdmsr
    orl     $(EFER_LME | EFER_NXE), %eax
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
    movl    $STACK_SIZE, %ecx
    mull    %ecx
    addl    $STACK_START, %eax
    movl    %eax, %esp
    movl    %eax, %ebp

    // Enable paging.
    movl    %cr0, %eax
    orl     $(CR0_PG | CR0_MP | CR0_ET | CR0_NE | CR0_WP), %eax
    movl    $(CR0_CD), %ebx
    notl    %ebx
    andl    %ebx, %eax
    movl    %eax, %cr0

    movb    $'C', %al
    movw    $0x3F8, %dx
    outb    %al, %dx

    ljmp    $(SEG_KCODE_64 << 3), $entry64

.p2align 2
gdt:
    .quad 0x0000000000000000          # Null Descriptor - should be present.
    .quad 0x00209A0000000000          # 64-bit code descriptor (exec/read).
    .quad 0x0000920000000000          # 64-bit data descriptor (read/write).

.align 4
    .word 0                           # Padding to make the "address of the GDT" field aligned on a 4-byte boundary

gdtdesc:
    .word gdt - . - 1                 # 16-bit Size (Limit) of GDT.
    .long gdt                         # 32-bit Base Address of GDT. (CPU will zero extend to 64-bit)


.code64  # Tell assembler to generate 64-bit code now.
entry64:
    movb    $'D', %al
    movw    $0x3F8, %dx
    outb    %al, %dx

    movw    $0x10, %ax
    movw    %ax, %ds
    movw    %ax, %es
    movw    %ax, %ss
    movw    %ax, %fs
    movw    %ax, %gs

    movb    $'E', %al
    movw    $0x3F8, %dx
    outb    %al, %dx

    movq    $NON_PRIMARY_KERNEL_MAIN, %rbx
    movq    (%rbx), %rax
    jmp     *%rax

loop:
    hlt
    jmp     loop
