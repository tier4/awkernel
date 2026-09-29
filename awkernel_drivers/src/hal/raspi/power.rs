use awkernel_lib::{delay::wait_forever, interrupt};
use core::sync::atomic::{AtomicUsize, Ordering};

/// Base address for the power management module.
pub static PM_BASE: AtomicUsize = AtomicUsize::new(0);

/// Set the base address for the PM module
///
/// # Safety
///
/// This function is unsafe because it modifies a static variable.
pub unsafe fn set_power_base(base: usize) {
    PM_BASE.store(base, Ordering::Relaxed);
}

/// Registers associated with the PM module
pub mod registers {
    use awkernel_lib::mmio_rw;

    mmio_rw!(offset 0x1c => pub PM_RSTC<u32>); // Reset controller register
    mmio_rw!(offset 0x20 => pub RSTS<u32>); // Reset status register
    mmio_rw!(offset 0x24 => pub PM_WDOG<u32>); // Watchdog register
}

/// Password required in the top byte of every `PM_RSTC`/`PM_RSTS`/`PM_WDOG` write for the hardware to accept it.
const PM_PASSWORD: u32 = 0x5a00_0000;

/// `PM_RSTC`'s reset-type field (bits [5:4]).
const PM_RSTC_WRCFG_MASK: u32 = 0x0000_0030;

/// `PM_RSTC` reset-type value that arms a full board reset once the watchdog countdown reaches zero.
const PM_RSTC_WRCFG_FULL_RESET: u32 = 0x0000_0020;

/// Boot-partition 63 encoded across `PM_RSTS`'s even low bits ([0], [2],
/// … [10]): `0x1 | 0x4 | 0x10 | 0x40 | 0x100 | 0x400`. 63 is the reserved
/// "halt" partition — the firmware treats it as "do not boot" rather than
/// a real partition to load, which is how [`shutdown`] stops the board
/// from rebooting after the reset. This is the same magic value Linux
/// writes to power a Pi off.
const PM_RSTS_HALT_PARTITION: u32 = 0x0000_0555;

/// A short watchdog countdown for a deliberate reset — long enough for the
/// register writes to take effect, short enough to be indistinguishable
/// from immediate (~150 µs at the 65536 Hz clock). Mirrors the count
/// Linux's driver loads for a software-requested restart.
const RESET_WDOG_TICKS: u32 = 10;

pub struct PowerManagement {
    base: usize,
}

impl PowerManagement {
    /// Creates a new instance of the Power Management module
    pub fn new() -> Self {
        let base = PM_BASE.load(Ordering::Relaxed);
        Self { base }
    }

    pub fn reboot(&self) -> ! {
        interrupt::disable();

        let wdog = PM_PASSWORD | RESET_WDOG_TICKS;
        registers::PM_WDOG.write(wdog, self.base);

        let mut rstc = registers::PM_RSTC.read(self.base);
        rstc = PM_PASSWORD | (rstc & !PM_RSTC_WRCFG_MASK) | PM_RSTC_WRCFG_FULL_RESET;
        registers::PM_RSTC.write(rstc, self.base);

        wait_forever();
    }

    /// Sets `PM_RSTS`'s boot-partition field to the reserved "halt" value (63), then reboots.
    /// On the way back up the firmware sees the halt sentinel and stops instead of booting, so
    /// the board goes idle and stays that way until it is physically power-cycled.
    pub fn shutdown(&self) -> ! {
        let mut rsts = registers::RSTS.read(self.base);
        rsts = PM_PASSWORD | (rsts & !PM_RSTS_HALT_PARTITION) | PM_RSTS_HALT_PARTITION;
        registers::RSTS.write(rsts, self.base);

        self.reboot();
    }
}

impl Default for PowerManagement {
    fn default() -> Self {
        Self::new()
    }
}

#[export_name = "__awkernel_reboot"]
extern "Rust" fn raspi_reboot() -> ! {
    PowerManagement::default().reboot()
}

#[export_name = "__awkernel_shutdown"]
extern "Rust" fn raspi_shutdown() -> ! {
    PowerManagement::default().shutdown()
}
