.section .boot, "x"
.global _start_cpu

_start_cpu:
.L1:
    hlt
    jmp .L1
