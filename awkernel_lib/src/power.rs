//! Board-level power control (reboot/shutdown).
//!
//! Boards provide their implementation by exporting `Rust`-ABI symbols named
//! `__awkernel_reboot` and `__awkernel_shutdown`. This module defines a weak
//! default that prints a "not supported" message, so a board that does not
//! implement power control still links successfully. A board crate (e.g.
//! `awkernel_drivers` for the Raspberry Pi) overrides the weak default with
//! a strong definition of the same symbol, which the linker prefers over the
//! weak one. x86_64 is implemented directly in this crate, since it only
//! depends on the ACPI tables already parsed here.
//!
//! This indirection means callers such as `awkernel_shell` never need to
//! know which board is being targeted, and adding a new board never
//! requires propagating a feature flag through the dependency graph.

extern "Rust" {
    fn __awkernel_reboot() -> !;
    fn __awkernel_shutdown() -> !;
}

/// Reboot the board.
pub fn reboot() -> ! {
    unsafe { __awkernel_reboot() }
}

/// Shut the board down.
pub fn shutdown() -> ! {
    unsafe { __awkernel_shutdown() }
}

#[cfg(not(all(feature = "x86", not(feature = "std"))))]
#[linkage = "weak"]
#[export_name = "__awkernel_reboot"]
extern "Rust" fn default_reboot() -> ! {
    crate::console::print("reboot is unsupported on this board\r\n");
    crate::delay::wait_forever()
}

#[cfg(not(all(feature = "x86", not(feature = "std"))))]
#[linkage = "weak"]
#[export_name = "__awkernel_shutdown"]
extern "Rust" fn default_shutdown() -> ! {
    crate::console::print("shutdown is unsupported on this board\r\n");
    crate::delay::wait_forever()
}
