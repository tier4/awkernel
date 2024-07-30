# Interrupt

The `Interrupt` trait provides a way to enable and disable interrupts.
It is defined in [awkernel_lib/src/interrupt.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/interrupt.rs) as follows.

```rust
pub trait Interrupt {
    fn get_flag() -> usize;
    fn disable();
    fn enable();
    fn set_flag(flag: usize);
}
```

The `get_flag` and `set_flag` methods get and set the interrupt flag.
These methods are used to save and restore the interrupt flag when enabling and disabling interrupts and used in the `InterruptGuard` structure.

# Interrupt Guard

The `InterruptGuard` structure  defined in [awkernel_lib/src/interrupt.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/interrupt.rs) is used to disable interrupts in a scope.
After the scope, interrupts are enabled automatically as follows.

```rust
{
    use awkernel_lib::interrupt::InterruptGuard;
    let _int_guard = InterruptGuard::new();
    // interrupts are disabled.
}
```

There are `enable` and `disable` functions in [awkernel_lib/src/interrupt.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/interrupt.rs).
You can use these functions rather than using the `InterruptGuard`.

# Implementation

## x86_64

For x86_64, the [`X86`](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/x86_64.rs) structure implements the `Interrupt` trait in
[awkernel_lib/src/arch/x86_64/interrupt.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/x86_64/interrupt.rs) as follows.

```rust
impl Interrupt for super::X86 {
    fn get_flag() -> usize {
        if x86_64::instructions::interrupts::are_enabled() {
            1
        } else {
            0
        }
    }

    fn disable() {
        x86_64::instructions::interrupts::disable();
    }

    fn enable() {
        x86_64::instructions::interrupts::enable();
    }

    fn set_flag(flag: usize) {
        if flag == 0 {
            x86_64::instructions::interrupts::disable();
        } else {
            x86_64::instructions::interrupts::enable();
        }
    }
}
```

For x86_64, Awkernel uses the [`x86_64`](https://docs.rs/x86_64/latest/x86_64/index.html) crate to enable and disable interrupts.

## AArch64

For x86_64, the [`AArch64`](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/aarch64.rs) structure implements the `Interrupt` trait in [awkernel_lib/src/arch/aarch64/interrupt.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/aarch64/interrupt.rs) as follows.

```rust
impl Interrupt for super::AArch64 {
    fn get_flag() -> usize {
        awkernel_aarch64::daif::get() as usize
    }

    fn disable() {
        unsafe { core::arch::asm!("msr daifset, #0b0010",) };
    }

    fn enable() {
        unsafe { core::arch::asm!("msr daifclr, #0b0010",) };
    }

    fn set_flag(flag: usize) {
        unsafe { awkernel_aarch64::daif::set(flag as u64) };
    }
}
```
