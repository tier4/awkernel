use super::clint::Clint;

// TODO: get info from device tree
static INTERRUPT_CONTROLLER: InterruptController = InterruptController {
    clint: Clint {
        base_addr: 0x0200_0000,
        mtime_freq: 10_000_000,
    },
};

pub struct InterruptController {
    clint: Clint,
}

#[inline]
pub(super) const fn clint() -> &'static Clint {
    &INTERRUPT_CONTROLLER.clint
}
