// M-mode trap entry for RV64.
//
// Saves the caller-saved registers plus mepc/mstatus, and dispatches to Rust.
// mepc and mstatus are saved because the handler may preempt the current task
// and another trap may occur before this frame is resumed.

  .section .text
  .align 4
  .global rv64_trap_entry
rv64_trap_entry:
  addi sp, sp, -144
  sd ra, 0(sp)
  sd t0, 8(sp)
  sd t1, 16(sp)
  sd t2, 24(sp)
  sd a0, 32(sp)
  sd a1, 40(sp)
  sd a2, 48(sp)
  sd a3, 56(sp)
  sd a4, 64(sp)
  sd a5, 72(sp)
  sd a6, 80(sp)
  sd a7, 88(sp)
  sd t3, 96(sp)
  sd t4, 104(sp)
  sd t5, 112(sp)
  sd t6, 120(sp)
  csrr t0, mepc
  sd t0, 128(sp)
  csrr t0, mstatus
  sd t0, 136(sp)

  csrr a0, mcause
  bltz a0, 1f

  # Exception: never returns.
  csrr a1, mepc
  csrr a2, mtval
  call riscv_handle_exception

1:
  # Interrupt
  call riscv_handle_interrupt

  ld t0, 136(sp)
  csrw mstatus, t0
  ld t0, 128(sp)
  csrw mepc, t0
  ld ra, 0(sp)
  ld t0, 8(sp)
  ld t1, 16(sp)
  ld t2, 24(sp)
  ld a0, 32(sp)
  ld a1, 40(sp)
  ld a2, 48(sp)
  ld a3, 56(sp)
  ld a4, 64(sp)
  ld a5, 72(sp)
  ld a6, 80(sp)
  ld a7, 88(sp)
  ld t3, 96(sp)
  ld t4, 104(sp)
  ld t5, 112(sp)
  ld t6, 120(sp)
  addi sp, sp, 144
  mret
