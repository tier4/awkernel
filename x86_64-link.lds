ENTRY(_start)
SECTIONS
{
  PROVIDE (__executable_start = SEGMENT_START("text-segment", 0x400000)); . = SEGMENT_START("text-segment", 0x400000) + SIZEOF_HEADERS;
  . = ALIGN(CONSTANT (MAXPAGESIZE));
  .init           :
  {
    KEEP (*(SORT_NONE(.init)))
  }
  .text           : { *(.text .text.* .gnu.linkonce.t*) }
  .fini           :
  {
    KEEP (*(SORT_NONE(.fini)))
  }

  . = ALIGN(CONSTANT (MAXPAGESIZE));
  __boot = .;
  .boot           : { *(.boot) }

  PROVIDE (__etext = .);
  PROVIDE (_etext = .);
  PROVIDE (etext = .);

  . = ALIGN(CONSTANT (MAXPAGESIZE));
  . = SEGMENT_START("rodata-segment", ALIGN(CONSTANT (MAXPAGESIZE)) + (. & (CONSTANT (MAXPAGESIZE) - 1)));
  .rodata         : { *(.rodata .rodata.* .gnu.linkonce.r.*) }
  .rodata1        : { *(.rodata1) }
  .eh_frame_hdr   : { *(.eh_frame_hdr) *(.eh_frame_entry .eh_frame_entry.*) }

  . = ALIGN(8);
  PROVIDE(__eh_frame = .);
  .eh_frame : { KEEP (*(.eh_frame)) *(.eh_frame.*) }

  . = DATA_SEGMENT_ALIGN (CONSTANT (MAXPAGESIZE), CONSTANT (COMMONPAGESIZE));
  .data           :
  {
    *(.data .data.* .gnu.linkonce.d*)
    SORT(CONSTRUCTORS)
  }
  .data1          : { *(.data1) }
  . = .;
  __bss_start = .;
  .bss (NOLOAD)   :
  {
   *(.dynbss)
   *(.bss .bss.*)
   *(COMMON)
   . = ALIGN(. != 0 ? 64 / 8 : 1);
  }
  . = ALIGN(64 / 8);
  _end = .; PROVIDE (end = .);

   /DISCARD/ : { *(.comment) *(.gnu*) *(.note*) }
}
