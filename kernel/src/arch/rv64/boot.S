// boot routine
  .text
  .section .init
  .align 3
  .global _start
  .type   _start, @function
  .attribute arch, "rv64gc"

_start:
  # set up the 8MB initial stack for each cpu.
  li sp, 0x80000000
  li a0, 0x00800000
  csrr a1, mhartid
  addi a1, a1, 1
  mul a0, a0, a1
  add sp, sp, a0
  # clear the BSS
  la t0, __bss_start
  la t1, __bss_end
1:
  sd zero, 0(t0)
  addi t0, t0, 8
  bltu t0, t1, 1b
  # jump to kernel_main
  jal ra, kernel_main
2:
  j 2b