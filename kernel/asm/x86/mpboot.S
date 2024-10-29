/*-
 * Copyright (c) 2000 The NetBSD Foundation, Inc.
 * All rights reserved.
 *
 * This code is derived from software contributed to The NetBSD Foundation
 * by RedBack Networks Inc.
 *
 * Author: Bill Sommerfeld
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE NETBSD FOUNDATION, INC. AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE FOUNDATION OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * Copyright (c) 1999 Stefan Grefen
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *      This product includes software developed by the NetBSD
 *      Foundation, Inc. and its contributors.
 * 4. Neither the name of The NetBSD Foundation nor the names of its
 *    contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY AUTHOR AND CONTRIBUTORS ``AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR AND CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/*
 * Copyright (c) 2006-2018 Frans Kaashoek, Robert Morris, Russ Cox,
 *                         Massachusetts Institute of Technology
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

// assembler macros to create x86 segments
#define SEG_NULLASM                                             \
        .word 0, 0;                                             \
        .byte 0, 0, 0, 0

#define SEG_ASM(type,base,lim,mode)                             \
        .word (((lim) >> 12) & 0xffff), ((base) & 0xffff);      \
        .byte (((base) >> 16) & 0xff), (0x90 | (type)),         \
                (mode | (((lim) >> 28) & 0xf)), (((base) >> 24) & 0xff)

#define STA_X 0x8 // Executable segment
#define STA_W 0x2 // Writeable (non-executable segments)
#define STA_R 0x2 // Readable (executable segments)

#define MODE_GD 0xC0 // G: granuarity 4KiB, D/B: 32-bit code and data
#define MODE_GL 0xA0 // G: granuarity 4KiB, L: 64-bit code segment

#define SEG_KCODE 3
#define SEG_KDATA 4

#define PSL_MBO 0x00000000  /* must be one bits */

// CR3 register

/*
 * Bits in 386 special registers:
 */
#define	CR0_PE  0x00000001  /* Protected mode Enable */
#define	CR0_MP  0x00000002  /* "Math" Present (NPX or NPX emulator) */
#define	CR0_EM  0x00000004  /* EMulate non-NPX coproc. (trap ESC only) */
#define	CR0_TS  0x00000008  /* Task Switched (if MP, trap ESC and WAIT) */
#define	CR0_ET  0x00000010  /* Extension Type (387 (if set) vs 287) */
#define	CR0_PG  0x80000000  /* PaGing enable */

/*
 * Bits in 486 special registers:
 */
#define CR0_NE  0x00000020  /* Numeric Error enable (EX16 vs IRQ13) */
#define CR0_WP  0x00010000  /* Write Protect (honor PG_RW in all modes) */
#define CR0_AM  0x00040000  /* Alignment Mask (set to enable AC flag) */
#define	CR0_NW  0x20000000  /* Not Write-through */
#define	CR0_CD  0x40000000  /* Cache Disable */

// CR4 register
#define CR4_VME         0x00000001  /* virtual 8086 mode extension enable */
#define CR4_PVI         0x00000002  /* protected mode virtual interrupt enable */
#define CR4_TSD         0x00000004  /* restrict RDTSC instruction to cpl 0 only */
#define CR4_DE          0x00000008  /* debugging extension */
#define CR4_PSE         0x00000010  /* large (4MB) page size enable */
#define CR4_PAE         0x00000020  /* physical address extension enable */
#define CR4_MCE         0x00000040  /* machine check enable */
#define CR4_PGE         0x00000080  /* page global enable */
#define CR4_PCE         0x00000100  /* enable RDPMC instruction for all cpls */
#define CR4_OSFXSR      0x00000200  /* enable fxsave/fxrestor and SSE */
#define CR4_OSXMMEXCPT  0x00000400  /* enable unmasked SSE exceptions */
#define CR4_UMIP        0x00000800  /* user mode instruction prevention */
#define CR4_VMXE        0x00002000  /* enable virtual machine operation */
#define CR4_SMXE        0x00004000  /* enable safe mode operation */
#define CR4_FSGSBASE    0x00010000  /* enable {RD,WR}{FS,GS}BASE ops */
#define CR4_PCIDE       0x00020000  /* enable process-context IDs */
#define CR4_OSXSAVE     0x00040000  /* enable XSAVE and extended states */
#define CR4_KL          0x00080000  /* enable AES Key Locker */
#define CR4_SMEP        0x00100000  /* supervisor mode exec protection */
#define CR4_SMAP        0x00200000  /* supervisor mode access prevention */
#define CR4_PKE         0x00400000  /* user-mode protection keys */
#define CR4_CET         0x00800000  /* control-flow enforcement tech */
#define CR4_PKS         0x01000000  /* supervisor-mode protection keys */
#define CR4_UINTR       0x02000000  /* user interrupts enable bit */

#define CPUID_NXE       0x00100000  /* No-Execute Extension */

// EFER
#define MSR_EFER    0xc0000080  /* Extended feature enable */
#define EFER_SCE    0x00000001  /* SYSCALL extension */
#define EFER_LME    0x00000100  /* Long Mode Active */
#define EFER_LMA    0x00000400  /* Long Mode Enabled */
#define EFER_NXE    0x00000800  /* No-Execute Enabled */
#define EFER_SVME   0x00001000  /* SVM Enabled */

#define NON_PRIMARY_KERNEL_MAIN (1024 * 2)
#define CPU0_CR3  (1024 * 2 +  8)
#define FLAG (1024 * 2 +  16)

#define CR0_DEFAULT	(CR0_PE|CR0_PG|CR0_NE|CR0_WP)
#define CR4_DEFAULT (CR4_PAE|CR4_PGE|CR4_PSE|CR4_OSFXSR|CR4_OSXMMEXCPT)

#define STACK_TEMP 4096
#define STACK_SIZE (2 * 1024 * 1024) // 2MiB
#define STACK_START (256 * 1024 * 1024) // 256MiB

.section .text

.global _start_cpu

.code16
_start_cpu:
    cli                          # BIOS enabled interrupts; disable

    mov	    %cs, %ax             # copy %cs to %ds.  Remember these
	mov	    %ax, %ds             # are offsets rather than selectors
	mov	    %ax, %ss

    # Find the relocation base
    xorl    %ebx, %ebx
    mov     %cs, %bx
    sall    $4, %ebx             # $ebx is the relocation base

    orl     %ebx, (gdtdesc32 + 2) # add the relocation base to the GDT
    orl     %ebx, (gdtdesc64 + 2) # add the relocation base to the GDT
    orl     %ebx, (ljmp32 + 2)    # add the relocation base to the ljmpl's argument, $start32
    orl     %ebx, (ljmp64 + 1)    # add the relocation base to the ljmpl's argument, $entry64

    addr32 lgdtl (gdtdesc32)

    movl    %cr0, %eax           # get cr0
    orl     $CR0_PE, %eax        # enable protected mode
    movl    %eax, %cr0           # doit

ljmp32:
    ljmpl   $0x8, $start32

.code32  # Tell assembler to generate 32-bit code now.
start32:

    movl    $0x10, %eax    # data segment
    movw    %ax, %ds
    movw    %ax, %ss
    movw    %ax, %es
    movw    %ax, %fs
    movw    %ax, %gs

    movl    $STACK_TEMP, %eax
    addl    %ebx, %eax
    movl    %eax, %esp

    /* First, reset the PSL. */
    pushl   $PSL_MBO
    popfl

    movl    %cr4, %eax
    orl     $(CR4_DEFAULT), %eax
    movl    %eax, %cr4

    movl    $MSR_EFER, %ecx
    rdmsr
    movl    %edx, %edi      # %edx is needed by wrmsr below
    movl    %ebx, %esi      # save relocation base

    # Check if we need to enable NXE
    movl    $0x80000001, %eax
    cpuid
    andl    $CPUID_NXE, %edx
    xorl    %eax, %eax
    testl   %edx, %edx
    jz      1f
    orl     $EFER_NXE, %eax
1:
    orl     $(EFER_LME | EFER_SCE), %eax

    movl    %edi, %edx      # Restore saved %edx
    movl    %esi, %ebx      # Restore saved %ebx

    movl    $MSR_EFER, %ecx
    wrmsr

    movl    $CPU0_CR3, %ecx
    orl     %ebx, %ecx
    movl    (%ecx), %ecx
    movl    %ecx, %cr3      # load ptd addr into mmu

    movl    $gdtdesc64, %eax
    orl     %ebx, %eax
    lgdt    (%eax)

    movl    %cr0, %ecx      # get control word
    orl     $CR0_DEFAULT, %ecx
    movl    %ecx, %cr0

ljmp64:
    ljmpl   $0x8, $entry64

.code64  # Tell assembler to generate 64-bit code now.
entry64:
    // Get local APIC ID.
    movl    $1, %eax
    cpuid

    test    $0x80000000, %ecx // check Hypervisor
    jnz     xapic

    test    $0x200000, %ecx    // Check if x2APIC is supported (bit 21 of ECX)
    jz      xapic

    // Get maximum CPUID leaf number
    xorl    %eax, %eax
    cpuid
    cmpl    $0x1F, %eax
    jb      use_leaf_0b

    // Use leaf 0x1F
    movl    $0x1F, %eax
    jmp     assign_apic_id

use_leaf_0b:
    movl    $0x0B, %eax

assign_apic_id:
    cpuid
    movl    %edx, %ebx
    jmp     end

xapic:
    shrl    $24, %ebx          // 31:24 is local APIC ID
    andl    $0xFF, %ebx

end:
    // APIC ID is now in EBX

    // Set stack pointer.
    movl    %ebx, %eax
    movl    $STACK_SIZE, %ecx
    mull    %ecx
    addl    $STACK_START, %eax
    movl    %eax, %esp
    movl    %eax, %ebp

    movq    $FLAG, %rax
    orq     %rsi, %rax      # Add the relocation base
    movq    $1, (%rax)

    movl    %esi, %ecx      # Restore saved relocation base
    orq     $NON_PRIMARY_KERNEL_MAIN, %rcx
    movq    (%rcx), %rax
    callq   *%rax

spin:
    hlt
    jmp     spin

# Bootstrap GDT
# force 4 byte alignment
.p2align 2
gdt32:
    SEG_NULLASM                                     # null seg
    SEG_ASM(STA_X|STA_R, 0x0, 0xffffffff, MODE_GD)  # 32-bit code seg
    SEG_ASM(STA_W, 0x0, 0xffffffff, MODE_GD)        # 32-bit data seg

gdtdesc32:
    .word   (gdtdesc32 - gdt32 - 1)                 # sizeof(gdt32) - 1
    .long   gdt32                                   # address gdt32

.p2align 2
gdt64:
	SEG_NULLASM
	SEG_ASM(STA_X|STA_R, 0x0, 0xffffffff, MODE_GL)  # 64-bit code seg
	SEG_ASM(STA_W, 0x0, 0xffffffff, MODE_GD)        # 64-bit data seg
gdtdesc64:
    .word   (gdtdesc64 - gdt64 - 1)                 # sizeof(gdt64) - 1
    .long   gdt64                                   # address gdt64
