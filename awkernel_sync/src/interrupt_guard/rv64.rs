#[inline(always)]
pub fn get_flag() -> usize {
    let x: usize;
    unsafe { core::arch::asm!("csrr {}, mstatus", out(reg) x) };
    x & 0x08
}

#[inline(always)]
pub fn disable() {
    let _x: usize;
    unsafe { core::arch::asm!("csrrc {}, mstatus, 0x08", out(reg) _x) };
}

#[inline(always)]
pub fn enable() {
    let _x: usize;
    unsafe { core::arch::asm!("csrrs {}, mstatus, 0x08", out(reg) _x) };
}

#[inline(always)]
pub fn set_flag(flag: usize) {
    if flag & 0x08 > 0 {
        enable();
    } else {
        disable();
    }
}
