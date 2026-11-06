OUTPUT_ARCH("riscv")
ENTRY(_start)

SECTIONS
{
    /* Boot code at DRAM start for -bios none */
    . = 0x80000000;
    PROVIDE (__executable_start = .);
    __ram_start = .;

    PROVIDE (stext = .);
    .init : { KEEP(*(.init)) }
    .text : { *(.text .text.* .gnu.linkonce.t*) }
    .fini           :
    {
        KEEP (*(SORT_NONE(.fini)))
    }
    PROVIDE (__etext = .);
    PROVIDE (_etext = .);
    PROVIDE (etext = .);
    PROVIDE (etext = .);

    /* Debug symbols need to be close to text for RISC-V PC-relative addressing */
    __debug_abbrev_start = .;
    __debug_abbrev_size = 0;
    __debug_info_start = .;
    __debug_info_size = 0;
    __debug_aranges_start = .;
    __debug_aranges_size = 0;
    __debug_ranges_start = .;
    __debug_ranges_size = 0;
    __debug_str_start = .;
    __debug_str_size = 0;
    __debug_line_start = .;
    __debug_line_size = 0;

    PROVIDE (srodata = .);
    .rodata : { *(.rodata .rodata.* .gnu.linkonce.r*) }
    PROVIDE (erodata = .);

    .eh_frame_hdr   : { *(.eh_frame_hdr) *(.eh_frame_entry .eh_frame_entry.*) }

    . = ALIGN(8);
    PROVIDE(__eh_frame = .);
    .eh_frame : { KEEP (*(.eh_frame)) *(.eh_frame.*) }

    PROVIDE(_data = .);
    PROVIDE(sdata = .);
    .data : ALIGN(1024 * 4) {
        __data_start = .;
        *(.data .data.* .gnu.linkonce.d*)
        __data_end = .;
    }
    PROVIDE(edata = .);
    PROVIDE(sbss_with_stack = .);
    .bss (NOLOAD) : ALIGN(1024 * 4) {
        __bss_start    = .;
        *(.bss .bss.*)
        *(COMMON)
        __bss_end = .;
    }
    PROVIDE(ebss = .);
    . = ALIGN(1024 * 4);
    PROVIDE(ekernel = .);

   /DISCARD/ : { *(.comment) *(.gnu*) *(.note*) *(.debug*) }
}
__bss_size = (__bss_end - __bss_start) >> 3;
