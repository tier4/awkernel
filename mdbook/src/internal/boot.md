# Boot

## x86_64

### Primary Core

The primary core calls `kernel_main` of `x86_64` first, which
is called by UEFI.

1. [kernel_main:kernel/arch/x86_64/kernel_main.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/x86_64/kernel_main.rs)
2. [main:kernel/main](https://github.com/tier4/awkernel/blob/main/kernel/src/main.rs)

During the primary core is booting,
it wakes up non-primary cores by sending ACPI's IPIs.

### Non-primary Cores

Non-primary cores calls `_start_cpu` defined in `mpboot.S` first, and it then calls `non_primary_kernel_main`.
It eventually calls `main` like the primary core.

1. [_start_cpu:kernel/asm/x86/mpboot.s](https://github.com/tier4/awkernel/blob/main/kernel/asm/x86/mpboot.S)
2. [non_primary_kernel_main:kernel/arch/x86_64/kernel_main.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/x86_64/kernel_main.rs)
3. [main:kernel/main](https://github.com/tier4/awkernel/blob/main/kernel/src/main.rs)
