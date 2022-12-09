.section .text
.global _entry32

_entry32:
    hlt
    jmp     _entry32
