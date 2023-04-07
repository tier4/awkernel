// start up routine, and initialization for C
  .text
  .align 2
  .global _start
  .type	_start, @function

 _start:
  li sp, 0x81000000 // set stack pointer
  jal ra, main      // call main, currently we do not implement BSS clear
1:
  ebreak            // ebreak (more formally, we should call _exit system call)
