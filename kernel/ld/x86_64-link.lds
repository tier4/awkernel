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

  PROVIDE (__etext = .);
  PROVIDE (_etext = .);
  PROVIDE (etext = .);

  . = ALIGN(CONSTANT (MAXPAGESIZE));
  . = SEGMENT_START("rodata-segment", ALIGN(CONSTANT (MAXPAGESIZE)) + (. & (CONSTANT (MAXPAGESIZE) - 1)));
  .rodata         : { 
    *(.rodata .rodata.* .gnu.linkonce.r.*)
    __debug_abbrev_start = .;
    *(.debug_abbrev)
    __debug_abbrev_size = . - __debug_abbrev_start;
    __debug_info_start = .;
    *(.debug_info)
    __debug_info_size = . - __debug_info_start;
    __debug_aranges_start = .;
    *(.debug_aranges)
    __debug_aranges_size = . - __debug_aranges_start;
    __debug_ranges_start = .;
    *(.debug_ranges)
    __debug_ranges_size = . - __debug_ranges_start;
    __debug_str_start = .;
    *(.debug_str)
    __debug_str_size = . - __debug_str_start;
    __debug_line_start = .;
    *(.debug_line)
    __debug_line_size = . - __debug_line_start;
    __debug_loc_start = .;
    *(.debug_loc)
    __debug_loc_size = . - __debug_loc_start;
  }
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
