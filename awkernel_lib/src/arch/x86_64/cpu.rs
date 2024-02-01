use crate::cpu::CPU;

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
