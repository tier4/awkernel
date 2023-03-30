use super::{acpi::AcpiMapper, page_allocator::PageAllocator};
use crate::{
    delay::{wait_forever, Delay},
    mmio_r, mmio_rw,
};
use acpi::AcpiTables;
use core::ptr::{read_volatile, write_volatile};
use x86_64::structures::paging::{OffsetPageTable, PageTableFlags};

mmio_r!(offset 0x00 => HPET_GENERAL_CAP<u64>);
mmio_rw!(offset 0x10 => HPET_GENERAL_CONF<u64>);
mmio_r!(offset 0xf0 => HPET_MAIN_COUNTER<u64>);

static mut HPET_BASE: usize = 0;
static mut HPET_COUNTER_HZ: u64 = 0;
static mut HPET_COUNTER_START: u64 = 0;

const HPET_GENERAL_CONF_NEABLE: u64 = 1;

pub(crate) struct ArchDelay;

impl Delay for ArchDelay {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("hlt") };
    }

    fn wait_microsec(usec: u64) {
        super::acpi::wait_usec(usec);
    }

    fn uptime() -> u64 {
        let base;
        let hz;
        let start;

        unsafe {
            base = read_volatile(&HPET_BASE);
            hz = read_volatile(&HPET_COUNTER_HZ);
            start = read_volatile(&HPET_COUNTER_START);
        }

        if hz == 0 {
            0
        } else {
            let now = HPET_MAIN_COUNTER.read(base);
            let diff = now - start;

            diff * 1_000_000 / hz
        }
    }

    fn cpu_counter() -> u64 {
        unsafe { core::arch::x86_64::_rdtsc() }
    }
}

pub(super) fn init(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator,
) {
    let hpet_info = acpi::hpet::HpetInfo::new(acpi).unwrap();

    if !hpet_info.main_counter_is_64bits() {
        log::error!("HPET's main count is not 64 bits.");
        super::delay::ArchDelay::wait_forever();
    }

    let base = hpet_info.base_address;

    log::info!("HPET base addres: 0x{:x}", base);

    let flags = PageTableFlags::PRESENT
        | PageTableFlags::WRITABLE
        | PageTableFlags::NO_EXECUTE
        | PageTableFlags::NO_CACHE;
    if !unsafe { super::mmu::map_to(base, base, flags, page_table, page_allocator) } {
        log::error!("Failed to map HPET's memory region.");
        wait_forever();
    }

    unsafe {
        // Store the base address.
        write_volatile(&mut HPET_BASE, base);

        // Calculate the frequency.
        let capabilities = HPET_GENERAL_CAP.read(base);
        let hz = 1_000_000_000_000_000 / (capabilities >> 32);
        log::info!("HPET frequency = {hz}[Hz]");
        write_volatile(&mut HPET_COUNTER_HZ, hz);

        // Enable HPET.
        let conf = HPET_GENERAL_CONF.read(base);
        HPET_GENERAL_CONF.write(conf | HPET_GENERAL_CONF_NEABLE, base);

        // Get and store the initial counter.
        let counter = HPET_MAIN_COUNTER.read(base);
        write_volatile(&mut HPET_COUNTER_START, counter);
    }
}
