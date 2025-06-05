OUTPUT_ARCH("riscv")
ENTRY(_start)

SECTIONS
{
    . = 0x80200000;
    PROVIDE (__executable_start = .);
    __ram_start = .;
    .init : { KEEP(*(.init)) }
    .text : { *(.text .text.* .gnu.linkonce.t*) }
    .fini           :
    {
        KEEP (*(SORT_NONE(.fini)))
    }
    PROVIDE (__etext = .);
    PROVIDE (_etext = .);
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

    .rodata : { *(.rodata .rodata.* .gnu.linkonce.r*) }

    .eh_frame_hdr   : { *(.eh_frame_hdr) *(.eh_frame_entry .eh_frame_entry.*) }

    . = ALIGN(8);
    PROVIDE(__eh_frame = .);
    .eh_frame : { KEEP (*(.eh_frame)) *(.eh_frame.*) }

    PROVIDE(_data = .);
    .data : ALIGN(1024 * 4) {
        __data_start = .;
        *(.data .data.* .gnu.linkonce.d*)
        __data_end = .;
    }
    .bss (NOLOAD) : ALIGN(1024 * 4) {
        __bss_start    = .;
        *(.bss .bss.*)
        *(COMMON)
        __bss_end = .;
    }
    . = ALIGN(1024 * 4);

   /DISCARD/ : { *(.comment) *(.gnu*) *(.note*) *(.debug*) }
}
__bss_size = (__bss_end - __bss_start) >> 3;
