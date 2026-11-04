# RV64 Context Switch

## Target

[awkernel_lib/src/context/rv64.rs](../../../../../awkernel_lib/src/context/rv64.rs).

## Subjects to be Verified

1. A context can be properly saved and restored.

## Detail

This specification is similar to [aarch64.tla](../aarch64/README.md) and [x86.tla](../x86/README.md).
Please see them beforehand.

### Target Functions

`save_context` and `restore_context` correspond to the first and second halves of `context_switch`, respectively.
They are implemented in RISC-V assembly (LP64D calling convention), and specified by procedures in PlusCal.
`a0` holds the address of the current context and `a1` holds the address of the next context.

The callee saved registers of LP64D are `ra`, `sp`, `s0`-`s11`, and `fs0`-`fs11`.
`sd`/`fsd` and `ld`/`fld` are modeled by the `sd` and `ld` macros, respectively.

The subject described above is verified as follows.

```
assert(callee_saved_registers = start_ctx);
```

## Context

`Context`, which is a structure, defined in [awkernel_lib/src/context/rv64.rs](../../../../../awkernel_lib/src/context/rv64.rs) can be represented by a sequence in TLA+ as follows.

```
[x \in 0..(SIZE_CONTEXT - 1) |-> 0]
```

`Context::gp_regs::ra` is at offset `0`, `Context::gp_regs::sp` is at offset `8`,
`Context::gp_regs::s0`-`s11` are at offsets `16`-`104`,
and `Context::fp_regs::fs0`-`fs11` are at offsets `112`-`200`.
Thus, `SIZE_CONTEXT` is `208`.
