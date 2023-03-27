pub fn cpu_id() -> usize {
    let ebx = unsafe { core::arch::x86_64::__cpuid(1).ebx };
    (ebx >> 24 & 0xff) as usize
}
