use bitflags::bitflags;

const KVM_CPUID_SIGNATURE: u32 = 0x40000000;
const KVM_CPUID_FEATURES: u32 = 0x40000001;

bitflags! {
    // https://github.com/openbsd/src/blob/48010215788d25a5802613d7ba22d657ef6b7049/sys/dev/pv/pvreg.h#L36
    pub struct KvmCpuidFeatures:u32 {
        const CLOCKSOURCE2          = 1 <<  3;
        const CLOCSOURCE_STABLE_BIT = 1 << 24;
    }
}

#[inline(always)]
fn is_kvm() -> bool {
    let cpuid = unsafe { core::arch::x86_64::__cpuid(KVM_CPUID_SIGNATURE) };
    // https://www.kernel.org/doc/html/v5.7/virt/kvm/cpuid.html
    cpuid.eax == 0x40000001
        && cpuid.ebx == 0x4b4d564b
        && cpuid.ecx == 0x564b4d56
        && cpuid.edx == 0x4d
}

#[inline(always)]
pub fn cpuid_features() -> Option<KvmCpuidFeatures> {
    if !is_kvm() {
        return None;
    }

    let cpuid = unsafe { core::arch::x86_64::__cpuid(KVM_CPUID_FEATURES) };
    Some(KvmCpuidFeatures::from_bits_retain(cpuid.eax))
}
