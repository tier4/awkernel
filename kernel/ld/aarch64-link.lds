ENTRY(_start)
SECTIONS
{
    PROVIDE (__executable_start = .);
    . = #INITADDR#; /* replaced by sed */
    __kernel_start = .;
    .init : { KEEP(*(.init)) }
    .text : { *(.text .text.* .gnu.linkonce.t*) }
    .fini           :
    {
        KEEP (*(SORT_NONE(.fini)))
    }
    PROVIDE (__etext = .);
    PROVIDE (_etext = .);
    PROVIDE (etext = .);

    .eh_frame_hdr : { *(.eh_frame_hdr) *(.eh_frame_entry .eh_frame_entry.*) }

  . = ALIGN(8);
    PROVIDE(__eh_frame = .);
    .eh_frame : { KEEP (*(.eh_frame)) *(.eh_frame.*) }

    . = ALIGN(1024 * 4);
    __data_start = .;

    .rodata : { *(.rodata .rodata.* .gnu.linkonce.r*) }

    PROVIDE(_data = .);
    .data : ALIGN(1024 * 4) {
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

    __stack_memory = .;

   /DISCARD/ : { *(.comment) *(.gnu*) *(.note*) }
}
__bss_size = (__bss_end - __bss_start) >> 3;
