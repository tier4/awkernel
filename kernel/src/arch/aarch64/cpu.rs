use awkernel_aarch64::mpidr_el1;

/// get my core index
pub fn core_pos() -> usize {
    let mpidr = mpidr_el1::get();
    mpidr as usize & 0xFF
}
