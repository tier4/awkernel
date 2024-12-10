#[inline(always)]
pub fn get_flag() -> usize {
    if x86_64::instructions::interrupts::are_enabled() {
        1
    } else {
        0
    }
}

#[inline(always)]
pub fn disable() {
    x86_64::instructions::interrupts::disable();
}

#[inline(always)]
pub fn set_flag(flag: usize) {
    if flag == 0 {
        x86_64::instructions::interrupts::disable();
    } else {
        x86_64::instructions::interrupts::enable();
    }
}
