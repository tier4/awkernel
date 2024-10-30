use super::{acpi::AcpiMapper, page_allocator::VecPageAllocator};
use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
    delay::{uptime, wait_forever, Delay},
    mmio_r, mmio_rw,
    paging::{Flags, PageTable},
};
use acpi::AcpiTables;
use core::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

mmio_r!(offset 0x00 => HPET_GENERAL_CAP<u64>);
mmio_rw!(offset 0x10 => HPET_GENERAL_CONF<u64>);
mmio_r!(offset 0xf0 => HPET_MAIN_COUNTER<u64>);

static HPET_BASE: AtomicUsize = AtomicUsize::new(0);
static HPET_COUNTER_START: AtomicU64 = AtomicU64::new(0);
static mut HPET_COUNTER_1_000_000_DIV_HZ: f64 = 0.0;

const HPET_GENERAL_CONF_ENABLE: u64 = 1;

impl Delay for super::X86 {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("hlt") };
    }

    fn wait_microsec(usec: u64) {
        let start = uptime();
        loop {
            let diff = uptime() - start;
            if diff >= usec {
                break;
            }

            core::hint::spin_loop();
        }
    }

    fn uptime() -> u64 {
        let base = HPET_BASE.load(Ordering::Relaxed);
        let factor = unsafe { HPET_COUNTER_1_000_000_DIV_HZ };
        let start = HPET_COUNTER_START.load(Ordering::Relaxed);

        if factor == 0.0 {
            0
        } else {
            let now = HPET_MAIN_COUNTER.read(base);
            let diff = now - start;

            (diff as f64 * factor) as u64
        }
    }

    fn cpu_counter() -> u64 {
        unsafe { core::arch::x86_64::_rdtsc() }
    }
}

pub(super) fn init(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut super::page_table::PageTable,
    page_allocator: &mut VecPageAllocator,
) {
    let hpet_info = acpi::hpet::HpetInfo::new(acpi).unwrap();

    if !hpet_info.main_counter_is_64bits() {
        log::error!("HPET's main count is not 64 bits.");
        wait_forever();
    }

    let base = hpet_info.base_address;
    let phy_base = PhyAddr::new(base);
    let virt_base = VirtAddr::new(base);

    log::info!("HPET base addres: 0x{:x}", base);

    let flags = Flags {
        write: true,
        execute: false,
        cache: false,
        write_through: false,
        device: true,
    };

    if unsafe {
        page_table
            .map_to(virt_base, phy_base, flags, page_allocator)
            .is_err()
    } {
        log::error!("Failed to map HPET's memory region.");
        wait_forever();
    }

    // Store the base address.
    HPET_BASE.store(base, Ordering::Relaxed);

    // Calculate the frequency.
    let capabilities = HPET_GENERAL_CAP.read(base);
    let hz = 1_000_000_000_000_000 / (capabilities >> 32);
    log::info!("HPET frequency = {hz}[Hz]");

    unsafe { HPET_COUNTER_1_000_000_DIV_HZ = 1_000_000.0 / hz as f64 };

    // Enable HPET.
    let conf = HPET_GENERAL_CONF.read(base);
    HPET_GENERAL_CONF.write(conf | HPET_GENERAL_CONF_ENABLE, base);

    // Get and store the initial counter.
    let counter = HPET_MAIN_COUNTER.read(base);
    HPET_COUNTER_START.store(counter, Ordering::Relaxed);
}
