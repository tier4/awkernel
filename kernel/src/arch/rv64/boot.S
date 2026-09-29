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
  mv tp, a0    # save hartid to thread pointer for later use

  # Preserve DTB pointer that QEMU/firmware passes in a1
  la t0, dtb_ptr
  sd a1, 0(t0)

  # set up a simple trap handler for M-mode
  la t0, early_trap_handler
  csrw mtvec, t0

  # Initialize mscratch to 0 (will be set properly later if needed)
  csrw mscratch, zero

  # set up the 8MB initial stack for each cpu.
  li sp, 0x80800000
  li t0, 0x00800000
  mv t1, a0    # use hartid
  addi t1, t1, 1
  mul t0, t0, t1
  add sp, sp, t0
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

# M-mode trap handler - handles interrupts and exceptions
.align 4
early_trap_handler:
  # Check if this is an interrupt or exception
  csrr t0, mcause
  blt t0, zero, handle_interrupt  # If MSB is set, it's an interrupt

  # This is an exception - print debug info and halt
  j unhandled_trap

handle_interrupt:
  # Get interrupt code (lower bits of mcause)
  li t1, 0x7FFFFFFFFFFFFFFF
  and t0, t0, t1

  # Check interrupt type
  li t1, 7  # M-mode timer interrupt
  beq t0, t1, handle_timer_interrupt

  li t1, 3  # M-mode software interrupt (IPI)
  beq t0, t1, handle_software_interrupt

  # Unknown interrupt - just return
  mret

handle_timer_interrupt:
  # Save all registers that might be clobbered by the Rust handler
  addi sp, sp, -256
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

  # Disable timer interrupt temporarily by setting mtimecmp to max
  # MTIMECMP base is 0x02004000, each hart has 8-byte register
  csrr t0, mhartid
  slli t0, t0, 3  # Multiply by 8
  li t1, 0x02004000
  add t0, t0, t1
  li t1, -1
  sd t1, 0(t0)

  # Call the Rust timer handler
  call riscv_handle_timer

  # Restore registers
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
  addi sp, sp, 256

  # Return from interrupt
  mret

handle_software_interrupt:
  # Save all registers that might be clobbered by the Rust handler
  addi sp, sp, -256
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

  # Clear the software interrupt by writing 0 to MSIP
  # MSIP base is 0x02000000, each hart has 4-byte register
  csrr t0, mhartid
  slli t0, t0, 2  # Multiply by 4
  li t1, 0x02000000
  add t0, t0, t1
  sw zero, 0(t0)   # Clear MSIP

  # Call the Rust IPI handler
  call riscv_handle_ipi

  # Restore registers
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
  addi sp, sp, 256

  # Return from interrupt
  mret

unhandled_trap:
  # Write 'TRAP!' to UART
  li t0, 0x10000000
  li t1, 'T'
  sb t1, 0(t0)
  li t1, 'R'
  sb t1, 0(t0)
  li t1, 'A'
  sb t1, 0(t0)
  li t1, 'P'
  sb t1, 0(t0)
  li t1, '!'
  sb t1, 0(t0)
  li t1, '\r'
  sb t1, 0(t0)
  li t1, '\n'
  sb t1, 0(t0)

  # Print mcause
  csrr a0, mcause
  call print_hex

  # Print mepc
  csrr a0, mepc
  call print_hex

  # Print mtval
  csrr a0, mtval
  call print_hex

  # Infinite loop
1:
  j 1b

# Helper function to print a hex value
print_hex:
  li t0, 0x10000000
  li t2, 60  # shift amount: 60, 56, 52, ..., 0
  li t3, 16  # counter
1:
  srl t1, a0, t2
  andi t1, t1, 0xF
  li t4, 10
  blt t1, t4, 2f
  addi t1, t1, 'A'-10
  j 3f
2:
  addi t1, t1, '0'
3:
  sb t1, 0(t0)
  addi t2, t2, -4
  addi t3, t3, -1
  bnez t3, 1b

  # Print newline
  li t1, '\r'
  sb t1, 0(t0)
  li t1, '\n'
  sb t1, 0(t0)
  ret

  .section .data
  .align 3
  .global dtb_ptr
dtb_ptr:
  .dword 0
