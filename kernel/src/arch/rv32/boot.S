// boot routine
  .text
  .section .init
  .align 2
  .global _start
  .type   _start, @function
  .attribute arch, "rv32imac"

_start:
  # set up the 4KB initial stack for each cpu.
  la sp, INITIAL_STACK
  li a0, 4096
  csrr a1, mhartid
  addi a1, a1, 1
  mul a0, a0, a1
  add sp, sp, a0
  # clear the BSS
  la t0, __bss_start
  la t1, __bss_end
1:
  sb zero, 0(t0)
  addi t0, t0, 1
  bleu t0, t1, 1b
  # jump to kernel_main
  jal ra, kernel_main
2:
  j 2b
