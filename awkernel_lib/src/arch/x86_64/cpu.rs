use crate::{
    cpu::{CPU, NUM_MAX_CPU},
    sync::rwlock::RwLock,
};
use alloc::collections::btree_map::BTreeMap;

static RAW_CPU_ID_TO_CPU_ID: RwLock<Option<BTreeMap<usize, usize>>> = RwLock::new(None);
static CPU_ID_TO_RAW_CPU_ID: RwLock<Option<BTreeMap<usize, usize>>> = RwLock::new(None);

static mut CPU_ID_NUMA_ID: [u8; NUM_MAX_CPU] = [0; NUM_MAX_CPU];

impl CPU for super::X86 {
    fn cpu_id() -> usize {
        let raw_cpu_id = Self::raw_cpu_id();
        if raw_cpu_id == 0 {
            return 0;
        }

        let mapping = RAW_CPU_ID_TO_CPU_ID.read();

        if let Some(mapping) = mapping.as_ref() {
            let id = mapping.get(&raw_cpu_id);
            if let Some(id) = id {
                return *id;
            }
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

    {
        let mut guard = CPU_ID_TO_RAW_CPU_ID.write();
        *guard = Some(cpu_id_to_raw_cpu_id);
    }

    let mut guard = RAW_CPU_ID_TO_CPU_ID.write();
    *guard = Some(mapping);
}

/// Get the raw CPU ID from the CPU ID.
pub fn cpu_id_to_raw_cpu_id(cpu_id: usize) -> Option<usize> {
    if cpu_id == 0 {
        return Some(0);
    }

    let guard = CPU_ID_TO_RAW_CPU_ID.read();
    if let Some(mapping) = guard.as_ref() {
        mapping.get(&cpu_id).copied()
    } else {
        None
    }
}

/// Get the CPU ID from the raw CPU ID.
pub fn raw_cpu_id_to_cpu_id(raw_cpu_id: usize) -> Option<usize> {
    if raw_cpu_id == 0 {
        return Some(0);
    }

    let guard = RAW_CPU_ID_TO_CPU_ID.read();
    if let Some(mapping) = guard.as_ref() {
        mapping.get(&raw_cpu_id).copied()
    } else {
        None
    }
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
pub fn cpu_id_to_numa(cpu_id: usize) -> usize {
    unsafe { CPU_ID_NUMA_ID[cpu_id] as usize }
}
