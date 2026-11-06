// boot routine
  .text
  .section .init
  .align 3
  .global _start
  .type   _start, @function
  .attribute arch, "rv64gc"

_start:
  # Read hart ID from mhartid CSR (M-mode)
  csrr a0, mhartid

  # set up the 8MB initial stack for each cpu.
  li sp, 0x80800000
  li t0, 0x00800000
  mv t1, a0    # use hartid
  addi t1, t1, 1
  mul t0, t0, t1
  add sp, sp, t0

  # Only hart 0 saves the DTB pointer and clears BSS.
  # Secondary harts skip straight to kernel_main and spin on
  # PRIMARY_INITIALIZED until hart 0 has finished boot setup.
  bnez a0, .Lskip_primary_init

  # Preserve DTB pointer that QEMU/firmware passes in a1 (hart 0 only)
  la t0, dtb_ptr
  sd a1, 0(t0)

  # clear the BSS (hart 0 only — avoids racing with PRIMARY_INITIALIZED)
  la t0, __bss_start
  la t1, __bss_end
1:
  sd zero, 0(t0)
  addi t0, t0, 8
  bltu t0, t1, 1b

  # Ensure BSS writes are visible before secondary harts read them
  fence w, rw

.Lskip_primary_init:
  # jump to kernel_main
  jal ra, kernel_main
2:
  j 2b

  .section .data
  .align 3
  .global dtb_ptr
dtb_ptr:
  .dword 0
