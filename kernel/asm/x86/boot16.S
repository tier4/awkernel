//
// assembler macros to create x86 segments
//

#define SEG_NULLASM                                             \
        .word 0, 0;                                             \
        .byte 0, 0, 0, 0

#define SEG_ASM(type,base,lim,mode)                             \
        .word (((lim) >> 12) & 0xffff), ((base) & 0xffff);      \
        .byte (((base) >> 16) & 0xff), (0x90 | (type)),         \
                (mode | (((lim) >> 28) & 0xf)), (((base) >> 24) & 0xff)

#define STA_X     0x8 // Executable segment
#define STA_W     0x2 // Writeable (non-executable segments)
#define STA_R     0x2 // Readable (executable segments)

#define MODE_GD 0xC0 // G: granuarity 4KiB, D/B: 32-bit code and data
#define MODE_GL 0xA0 // G: granuarity 4KiB, L: 64-bit code segment

#define SEG_KCODE 1
#define SEG_KDATA 2

// Control Register flags
#define CR0_PE    0x00000001 // Protection Enable

#define ENTRY32 (1024 * 5)

.section .text

.global _start_cpu

.code16
_start_cpu:
    cli                         # BIOS enabled interrupts; disable

    # Zero data segment registers DS, ES, and SS.
    xorw    %ax, %ax             # Set %ax to zero
    movw    %ax, %ds             # -> Data Segment
    movw    %ax, %es             # -> Extra Segment
    movw    %ax, %ss             # -> Stack Segment

    # Physical address line A20 is tied to zero so that the first PCs
    # with 2 MB would run software that assumed 1 MB.  Undo that.
seta20.1:
    inb     $0x64, %al               # Wait for not busy
    testb   $0x2, %al
    jnz     seta20.1

    movb    $0xd1, %al               # 0xd1 -> port 0x64
    outb    %al, $0x64

seta20.2:
    inb     $0x64, %al               # Wait for not busy
    testb   $0x2, %al
    jnz     seta20.2

    movb    $0xdf, %al               # 0xdf -> port 0x60
    outb    %al, $0x60

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

    # Jump to ENTRY32
    movl    $ENTRY32, %eax
    jmp     *%eax

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
    SEG_ASM(STA_X|STA_R, 0x0, 0xffffffff, MODE_GD)   # 32-bit code seg
    SEG_ASM(STA_W, 0x0, 0xffffffff, MODE_GD)         # 32-bit data seg
    SEG_ASM(STA_X|STA_R, 0x0, 0xffffffff, MODE_GL)   # 64-bit code seg

gdtdesc:
    .word   (gdtdesc - gdt - 1)             # sizeof(gdt) - 1
    .long   gdt                             # address gdt
