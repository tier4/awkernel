//
// assembler macros to create x86 segments
//

#define SEG_NULLASM                                             \
        .word 0, 0;                                             \
        .byte 0, 0, 0, 0

// The 0xC0 means the limit is in 4096-byte units
// and (for executable segments) 32-bit mode.
#define SEG_ASM(type,base,lim)                                  \
        .word (((lim) >> 12) & 0xffff), ((base) & 0xffff);      \
        .byte (((base) >> 16) & 0xff), (0x90 | (type)),         \
                (0xC0 | (((lim) >> 28) & 0xf)), (((base) >> 24) & 0xff)

#define STA_X     0x8 // Executable segment
#define STA_W     0x2 // Writeable (non-executable segments)
#define STA_R     0x2 // Readable (executable segments)

#define SEG_KCODE 1
#define SEG_KDATA 2

// Control Register flags
#define CR0_PE    0x00000001 // Protection Enable

.section .text

.global _start_cpu

// Address of _start_cpu
#define ADDR_OFFSET 0x1000

.code16
_start_cpu:
    cli                         # BIOS enabled interrupts; disable

    # Zero data segment registers DS, ES, and SS.
    xorw    %ax,%ax             # Set %ax to zero
    movw    %ax,%ds             # -> Data Segment
    movw    %ax,%es             # -> Extra Segment
    movw    %ax,%ss             # -> Stack Segment

    # Switch from real to protected mode.  Use a bootstrap GDT that makes
    # virtual addresses map directly to physical addresses so that the
    # effective memory map doesn't change during the transition.
    lgdt    gdtdesc
    movl    %cr0, %eax
    orl     $CR0_PE, %eax
    movl    %eax, %cr0

//PAGEBREAK!
    # Complete the transition to 32-bit protected mode by using a long jmp
    # to reload %cs and %eip.  The segment descriptors are set up with no
    # translation, so that the mapping is still the identity mapping.
    ljmp    $(SEG_KCODE<<3), $start32

.code32  # Tell assembler to generate 32-bit code now.
start32:
    # Set up the protected-mode data segment registers
    movw    $(SEG_KDATA<<3), %ax    # Our data segment selector
    movw    %ax, %ds                # -> DS: Data Segment
    movw    %ax, %es                # -> ES: Extra Segment
    movw    %ax, %ss                # -> SS: Stack Segment
    movw    $0, %ax                 # Zero segments not ready for use
    movw    %ax, %fs                # -> FS
    movw    %ax, %gs                # -> GS

    # Set up the stack pointer and call into C.
    # movl    $start, %esp
    # call    bootmain

    # If bootmain returns (it shouldn't), trigger a Bochs
    # breakpoint if running under Bochs, then loop.
    movw    $0x8a00, %ax            # 0x8a00 -> port 0x8a00
    movw    %ax, %dx
    outw    %ax, %dx
    movw    $0x8ae0, %ax            # 0x8ae0 -> port 0x8a00
    outw    %ax, %dx
spin:
    hlt
    jmp     spin

# Bootstrap GDT
.p2align 2                                  # force 4 byte alignment
gdt:
    SEG_NULLASM                             # null seg
    SEG_ASM(STA_X|STA_R, 0x0, 0xffffffff)   # code seg
    SEG_ASM(STA_W, 0x0, 0xffffffff)         # data seg

gdtdesc:
    .word   (gdtdesc - gdt - 1)             # sizeof(gdt) - 1
    .long   gdt                             # address gdt
