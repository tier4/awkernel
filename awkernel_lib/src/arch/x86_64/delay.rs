use super::{acpi::AcpiMapper, cpu::cpu_id_to_numa, page_allocator::VecPageAllocator};
use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
    cpu::{cpu_id, raw_cpu_id},
    delay::{uptime, wait_forever, Delay},
    mmio_r, mmio_rw,
    paging::{Flags, PageTable},
};
use acpi::AcpiTables;
use core::sync::{
    self,
    atomic::{AtomicI64, AtomicU64, AtomicUsize, Ordering},
};

mmio_r!(offset 0x00 => HPET_GENERAL_CAP<u64>);
mmio_rw!(offset 0x10 => HPET_GENERAL_CONF<u64>);
mmio_r!(offset 0xf0 => HPET_MAIN_COUNTER<u64>);

static HPET_BASE: AtomicUsize = AtomicUsize::new(0);
static HPET_COUNTER_START: AtomicU64 = AtomicU64::new(0);

static mut HPET_MULTIPLIER_NANO: u128 = 0;

static RDTSC_COUNTER_START: AtomicU64 = AtomicU64::new(0);
static mut RDTSC_FREQ: u128 = 0;

static CPU0_RDTSC: AtomicU64 = AtomicU64::new(0);
static RDTSC_OFFSET: [AtomicI64; 16] = array_macro::array![_ => AtomicI64::new(0); 16];

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
        (Self::uptime_nano() / 1_000) as u64
    }

    fn uptime_nano() -> u128 {
        let now = read_rdtsc();
        let start = RDTSC_COUNTER_START.load(Ordering::Relaxed);
        let hz = unsafe { RDTSC_FREQ };

        if hz == 0 {
            return 0;
        }

        let id = cpu_id();
        let numa_id = cpu_id_to_numa(id);

        let now = if numa_id != 0 {
            let offset = RDTSC_OFFSET[numa_id].load(Ordering::Relaxed);
            if offset < 0 {
                now - offset.unsigned_abs()
            } else {
                now + offset as u64
            }
        } else {
            now
        };

        let diff = now - start;
        diff as u128 * 1_000_000_000 / hz
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
    unsafe { HPET_MULTIPLIER_NANO = 1_000_000_000 / (hz as u128) };

    // Enable HPET.
    let conf = HPET_GENERAL_CONF.read(base);
    HPET_GENERAL_CONF.write(conf | HPET_GENERAL_CONF_ENABLE, base);

    // Get and store the initial counter.
    let counter = HPET_MAIN_COUNTER.read(base);
    HPET_COUNTER_START.store(counter, Ordering::Relaxed);

    // Calculate RDTSC frequency.
    let t0 = read_rdtsc();
    hpet_wait_nano(100_000_000);
    let t1 = read_rdtsc();

    let hz = (t1 - t0) as u128 * 10;
    log::info!("RDTSC Frequency = {} Hz", hz);

    unsafe { RDTSC_FREQ = hz };

    // Initialize RDTSC counter.
    let counter = read_rdtsc();
    RDTSC_COUNTER_START.store(counter, Ordering::Relaxed);
}

#[inline(always)]
fn hpet_uptime_nano() -> u128 {
    let base = HPET_BASE.load(Ordering::Relaxed);
    let start = HPET_COUNTER_START.load(Ordering::Relaxed);

    unsafe {
        if HPET_MULTIPLIER_NANO == 0 {
            0
        } else {
            let now = HPET_MAIN_COUNTER.read(base);
            let diff = (now - start) as u128;

            diff * HPET_MULTIPLIER_NANO
        }
    }
}

#[inline(always)]
fn hpet_wait_nano(nsec: u128) {
    let start = hpet_uptime_nano();
    loop {
        let diff = hpet_uptime_nano() - start;
        if diff >= nsec {
            break;
        }

        core::hint::spin_loop();
    }
}

#[inline(always)]
fn read_rdtsc() -> u64 {
    sync::atomic::fence(Ordering::Acquire);
    let now = unsafe { core::arch::x86_64::_rdtsc() };
    sync::atomic::fence(Ordering::Release);

    now
}

/// Synchronize the RDTSC counter.
/// Calculate the offset between the RDTSC counter of CPU0 and other CPUs.
///
/// # Safety
///
/// This function must be called during the kernel initialization.
pub unsafe fn synchronize_rdtsc() {
    let raw_cpu_id = raw_cpu_id();
    let numa_id = cpu_id_to_numa(raw_cpu_id);

    if raw_cpu_id != 0 && numa_id == 0 {
        return;
    }

    if raw_cpu_id == 0 {
        CPU0_RDTSC.store(read_rdtsc(), Ordering::Relaxed);
    } else {
        let cpu0_rdtsc = loop {
            let cpu0_rdtsc = CPU0_RDTSC.load(Ordering::Relaxed);
            if cpu0_rdtsc != 0 {
                break cpu0_rdtsc;
            }
        };

        let now = read_rdtsc();

        let diff = if now <= cpu0_rdtsc {
            (cpu0_rdtsc - now) as i64
        } else {
            (now - cpu0_rdtsc) as i64
        };

        RDTSC_OFFSET[numa_id].store(diff, Ordering::Relaxed);
    }
}
