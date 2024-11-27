use crate::cpu::{CPU, NUM_MAX_CPU};
use alloc::collections::btree_map::BTreeMap;

#[derive(Debug, Clone, Copy)]
struct RawCpuIdAndCpuId {
    raw_cpu_id: usize,
    cpu_id: usize,
}

static mut CPU_ID_NUMA_ID: [u8; NUM_MAX_CPU] = [0; NUM_MAX_CPU];

static mut RAW_CPU_ID_AND_CPU_ID: [RawCpuIdAndCpuId; NUM_MAX_CPU] = [RawCpuIdAndCpuId {
    raw_cpu_id: 0,
    cpu_id: 0,
}; NUM_MAX_CPU];

impl CPU for super::X86 {
    fn cpu_id() -> usize {
        let raw_cpu_id = Self::raw_cpu_id();
        if raw_cpu_id == 0 {
            return 0;
        }

        if let Some(id) = raw_cpu_id_to_cpu_id(raw_cpu_id) {
            return id;
        }

        panic!(
            "CPU ID mapping is not set for CPU ID {}",
            Self::raw_cpu_id()
        );
    }

    fn raw_cpu_id() -> usize {
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
}

/// Set the raw CPU ID to CPU ID mapping.
///
/// # Safety
///
/// This function must be called before at the beginning of the kernel.
pub unsafe fn set_raw_cpu_id_to_cpu_id(mapping: BTreeMap<usize, usize>) {
    let mut cpu_id_to_raw_cpu_id = BTreeMap::new();
    for (raw_cpu_id, cpu_id) in mapping.iter() {
        cpu_id_to_raw_cpu_id.insert(*cpu_id, *raw_cpu_id);
    }

    for (raw_cpu_id, cpu_id) in mapping.iter() {
        unsafe {
            RAW_CPU_ID_AND_CPU_ID[*cpu_id] = RawCpuIdAndCpuId {
                raw_cpu_id: *raw_cpu_id,
                cpu_id: *cpu_id,
            };
        }
    }
}

/// Get the raw CPU ID from the CPU ID.
#[inline(always)]
pub fn cpu_id_to_raw_cpu_id(cpu_id: usize) -> Option<usize> {
    if cpu_id == 0 {
        return Some(0);
    }

    unsafe {
        let ptr = &raw const RAW_CPU_ID_AND_CPU_ID;
        let r = &*ptr;
        for ids in r.iter() {
            if ids.cpu_id == cpu_id {
                return Some(ids.raw_cpu_id);
            }
        }
    }

    None
}

/// Get the CPU ID from the raw CPU ID.
#[inline(always)]
pub fn raw_cpu_id_to_cpu_id(raw_cpu_id: usize) -> Option<usize> {
    if raw_cpu_id == 0 {
        return Some(0);
    }

    unsafe {
        let ptr = &raw const RAW_CPU_ID_AND_CPU_ID;
        let r = &*ptr;
        for ids in r.iter() {
            if ids.raw_cpu_id == raw_cpu_id {
                return Some(ids.cpu_id);
            }
        }
    }

    None
}

/// Set the raw CPU ID to NUMA ID mapping.
///
/// # Safety
///
/// This function must be called before at the beginning of the kernel.
pub unsafe fn set_raw_cpu_id_to_numa(mapping: BTreeMap<u32, u32>) {
    for (raw_cpu_id, numa_id) in mapping.iter() {
        if let Some(id) = raw_cpu_id_to_cpu_id(*raw_cpu_id as usize) {
            unsafe {
                CPU_ID_NUMA_ID[id] = *numa_id as u8;
            }
        }
    }
}

/// Get the NUMA ID from the raw CPU ID.
#[inline(always)]
pub fn cpu_id_to_numa(cpu_id: usize) -> usize {
    unsafe { CPU_ID_NUMA_ID[cpu_id] as usize }
}
