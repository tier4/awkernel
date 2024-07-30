# CPU

The `CPU` trait provides a way to get the current CPU ID.
It is defined in [awkernel_lib/src/cpu.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/cpu.rs) as follows.

```rust
pub trait CPU {
    /// CPU ID returns the ID of the CPU.
    /// The ID is unique for each CPU and starts from 0 to `num_cpu() - 1`.
    fn cpu_id() -> usize;

    /// Raw CPU ID returns the ID of the CPU without any modification.
    fn raw_cpu_id() -> usize;
}
```

The `cpu_id` method returns the current CPU ID.
The ID is unique for each CPU and ranges from `0` to `num_cpu() - 1`.
The `num_cpu` function, which returns the number of CPUs,
is also defined in [awkernel_lib/src/cpu.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/cpu.rs).

The `raw_cpu_id` method returns the ID of the CPU without any modification.
The ID is unique for each CPU,
but it may not be in the range of `0` to `num_cpu() - 1`.

There are functions regarding CPU in [awkernel_lib/src/cpu.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/cpu.rs) as follows.

|  function             | description |
|-----------------------|-------------|
| `fn cpu_id() -> usize` | Return the ID of the CPU. |
| `fn raw_cpu_id() -> usize` | Return the ID of the CPU without any modification. |
| `fn num_cpu() -> usize` | Return the number of CPUs. |

# Implementation

## x86_64

For x86_64, the [`X86`](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/x86_64.rs) structure implements the `CPU` trait in
[awkernel_lib/src/arch/x86_64/cpu.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/x86_64/cpu.rs) as follows.

```rust
impl CPU for super::X86 {
    fn cpu_id() -> usize {
        let cpuid_leaf_1 = unsafe { core::arch::x86_64::__cpuid(1) };

        // Check if x2APIC is supported
        if (cpuid_leaf_1.ecx & (1 << 21)) != 0 {
            // Get x2APIC ID from leaf 1FH or leaf 0BH (1FH is preferred)
            let max_leaf = unsafe { core::arch::x86_64::__cpuid(0) }.eax;
            let edx = if max_leaf >= 0x1F {
                unsafe { core::arch::x86_64::__cpuid(0x1F).edx }
            } else {
                unsafe { core::arch::x86_64::__cpuid(0x0B).edx }
            };
            edx as usize
        } else {
            (cpuid_leaf_1.ebx >> 24 & 0xff) as usize
        }
    }

    fn raw_cpu_id() -> usize {
        Self::cpu_id()
    }
}
```

Awkernel uses `core::arch::x86_64::__cpuid` to get the CPU ID.
It assumes that the CPU ID is unique for each CPU and ranges from `0` to `num_cpu() - 1`.
If you find any hardware that does not follow this assumption,
please let us know or send us a PR.

## AArch64

For x86_64, the [`AArch64`](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/aarch64.rs) structure implements the `CPU` trait in [awkernel_lib/src/arch/aarch64/cpu.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/aarch64/cpu.rs) as follows.

```rust
impl CPU for super::AArch64 {
    fn cpu_id() -> usize {
        let mpidr = mpidr_el1::get();

        let aff0 = mpidr & 0xff;
        let aff1 = (mpidr >> 8) & 0xff;
        let aff2 = (mpidr >> 16) & 0xff;
        let aff3 = (mpidr >> 32) & 0xff;

        let result =
            unsafe { aff0 + AFF0_MAX * aff1 + AFF0_X_AFF1 * aff2 + AFF0_X_AFF1_X_AFF2 * aff3 };

        result as usize
    }

    fn raw_cpu_id() -> usize {
        mpidr_el1::get() as usize
    }
}
```
For AArch64, Awkernel calculates the CPU ID based on the `MPIDR_EL1` register and the affinity information variables.
