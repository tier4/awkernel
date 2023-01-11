use super::acpi::AcpiMapper;
use crate::{delay::Delay, mmio_r, mmio_rw};
use acpi::AcpiTables;
use core::{
    arch::x86_64::_mm_pause,
    ptr::{read_volatile, write_volatile},
};

mmio_r!(offset 0x00 => hpet_general_cap<u64>);
mmio_rw!(offset 0x10 => hpet_general_conf<u64>);
mmio_r!(offset 0xf0 => hpet_main_counter<u64>);

static mut HPET_BASE: usize = 0;
static mut HPET_COUNTER_HZ: u64 = 0;
static mut HPET_COUNTER_START: u64 = 0;

const HPET_GENERAL_CONF_NEABLE: u64 = 1;

pub struct ArchDelay;

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
            let now = hpet_main_counter(base).read();
            let diff = now - start;

            diff * 1000_000 / hz as u64
        }
    }

    fn cpu_counter() -> u64 {
        unsafe { core::arch::x86_64::_rdtsc() }
    }
}

pub(super) fn init(acpi: &AcpiTables<AcpiMapper>, offset: u64) {
    let offset = offset as usize;
    let hpet_info = acpi::hpet::HpetInfo::new(&acpi).unwrap();

    if !hpet_info.main_counter_is_64bits() {
        log::error!("HPET's main count is not 64 bits.");
        // super::delay::ArchDelay::wait_forever();
    }

    let base = hpet_info.base_address + offset;

    unsafe {
        // Store the base address.
        write_volatile(&mut HPET_BASE, base);

        // Calculate the frequency.
        let capabilities = hpet_general_cap(base).read();
        let hz = 1000_000_000_000_000 / (capabilities >> 32);
        log::info!("HPET frequency = {hz}[Hz]");
        write_volatile(&mut HPET_COUNTER_HZ, hz);

        // Enable HPET.
        let conf = hpet_general_conf(base).read();
        hpet_general_conf(base).write(conf | HPET_GENERAL_CONF_NEABLE);

        // Get and store the initial counter.
        let counter = hpet_main_counter(base).read();
        write_volatile(&mut HPET_COUNTER_START, counter);
    }
}
