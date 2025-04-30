use super::{acpi::AcpiMapper, kvm::pvclock, page_allocator::VecPageAllocator};
use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
    cpu::cpu_id,
    delay::{uptime, Delay},
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

static TSC_COUNTER_START: AtomicU64 = AtomicU64::new(0);
static mut TSC_FREQ: u128 = 0;

const HPET_GENERAL_CONF_ENABLE: u64 = 1;

impl Delay for super::X86 {
    fn wait_interrupt() {
        unsafe { core::arch::asm!("hlt") };
    }

    fn wait_microsec(usec: u64) {
        let start = uptime();
        loop {
            let t = uptime();

            if t < start {
                core::hint::spin_loop();
                continue;
            }

            let diff = t - start;
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
        if let Some(t) = pvclock::uptime_nano() {
            return t as u128;
        }

        let now = read_tsc();
        let start = TSC_COUNTER_START.load(Ordering::Relaxed);
        let hz = unsafe { TSC_FREQ };

        if hz == 0 {
            return 0;
        }

        if now < start {
            return 0;
        }

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
) -> Result<(), &'static str> {
    if pvclock::init().is_ok() {
        log::info!("Pvclock is used for uptime().");
    } else {
        init_hpet(acpi, page_table, page_allocator)?;

        // Initialize TSC counter.
        let counter = read_tsc();
        TSC_COUNTER_START.store(counter, Ordering::Relaxed);
    }

    Ok(())
}

fn init_hpet(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut super::page_table::PageTable,
    page_allocator: &mut VecPageAllocator,
) -> Result<(), &'static str> {
    let hpet_info = acpi::hpet::HpetInfo::new(acpi).or(Err("HPET is not available"))?;

    if !hpet_info.main_counter_is_64bits() {
        return Err("HPET's main count is not 64 bits.");
    }

    let base = hpet_info.base_address;
    let phy_base = PhyAddr::new(base);
    let virt_base = VirtAddr::new(base);

    log::info!("HPET base addres: 0x{base:x}");

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
        return Err("Failed to map HPET's memory region.");
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

    // Calculate TSC frequency.
    let t0 = read_tsc();
    hpet_wait_nano(100_000_000);
    let t1 = read_tsc();

    let hz = (t1 - t0) as u128 * 10;
    log::info!("TSC Frequency (HPET) = {hz} Hz");

    unsafe { TSC_FREQ = hz };

    Ok(())
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
pub(super) fn read_tsc() -> u64 {
    sync::atomic::fence(Ordering::Acquire);
    let now = unsafe { core::arch::x86_64::_rdtsc() };
    sync::atomic::fence(Ordering::Release);

    now
}

// Synchronize TSCs between CPUs.

const IA32_TIME_STAMP_COUNTER: u32 = 0x10;
const SYNCRHONIZE_TRIES: usize = 11;
static NEXT_CPU: AtomicUsize = AtomicUsize::new(1);

static CHANNEL_CPU0_RX: AtomicI64 = AtomicI64::new(MSG_NULL);
static CHANNEL_CPU0_TX: AtomicI64 = AtomicI64::new(MSG_NULL);

static MSG_NULL: i64 = i64::MIN;
static MSG_START: i64 = i64::MIN + 1;
static MSG_OK: i64 = i64::MIN + 2;
static MSG_END: i64 = i64::MIN + 3;

/// Synchronize the TSC.
/// Calculate the offset between the TSC of CPU0 and other CPUs.
///
/// # Algorithm
///
/// ## Synchronization
///
/// ```text
///   CPU 0         CPU X
///     |<-- start ---|
///     |----- OK --->|
///  t1 |<--- t0 -----| t0
///  t2 |-- t1 + t2 ->| t3, offset = ((t1 - t0) + (t2 - t3)) / 2
/// ```
///
/// ## Finalization
///
/// ```text
///   CPU 0         CPU X
///     |<--- end ----|
/// ```
///
/// # Safety
///
/// This function must be called during the kernel initialization.
pub unsafe fn synchronize_tsc(num_cpu: usize) {
    if super::kvm::pvclock::available() {
        return;
    }

    let cpu_id = cpu_id();

    if cpu_id == 0 {
        loop {
            // Receive MSG_START
            let msg = cpu_0_get_rx();
            if msg == MSG_END {
                log::info!("Synchronized TSCs.");
                return;
            }

            assert_eq!(msg, MSG_START);

            // Send MSG_OK
            cpu_0_put_tx(MSG_OK);

            // Receive t0
            let _t0 = cpu_0_get_rx();

            let t1 = read_tsc() as i64;

            // Send t1 + t2
            cpu_0_put_tx(t1 * 2);
        }
    } else {
        while NEXT_CPU.load(Ordering::Relaxed) != cpu_id {
            core::hint::spin_loop();
        }

        let mut offsets = [0; SYNCRHONIZE_TRIES];

        for offset in offsets.iter_mut() {
            // Send MSG_START
            cpu_x_put_rx(MSG_START);

            // Receive MSG_OK
            cpu_x_wait_tx(MSG_OK);

            let t0 = read_tsc() as i64;

            // Send t0
            cpu_x_put_rx(t0);

            // Receive t1 + t2
            let t1t2 = cpu_x_get_tx();

            let t3 = read_tsc() as i64;
            *offset = (t1t2 - t0 - t3) / 2;
        }

        offsets.sort_unstable();
        let offset = offsets[SYNCRHONIZE_TRIES / 2];
        let tsc = read_tsc() as i64 + offset;
        x86_64::registers::model_specific::Msr::new(IA32_TIME_STAMP_COUNTER).write(tsc as u64);

        if cpu_id < num_cpu - 1 {
            NEXT_CPU.fetch_add(1, Ordering::Relaxed);
        } else {
            cpu_x_put_rx(MSG_END);
        }
    }
}

/// CPUX sends a message to CPU0.
#[inline(always)]
fn cpu_x_put_rx(msg: i64) {
    while CHANNEL_CPU0_RX
        .compare_exchange(MSG_NULL, msg, Ordering::Relaxed, Ordering::Relaxed)
        .is_err()
    {
        core::hint::spin_loop();
    }
}

/// CPU0 sends a message to CPUX.
#[inline(always)]
fn cpu_0_put_tx(msg: i64) {
    while CHANNEL_CPU0_TX
        .compare_exchange(MSG_NULL, msg, Ordering::Relaxed, Ordering::Relaxed)
        .is_err()
    {
        core::hint::spin_loop();
    }
}

/// CPU0 waits for a message from CPUX.
#[inline(always)]
fn cpu_x_wait_tx(msg: i64) {
    while CHANNEL_CPU0_TX
        .compare_exchange(msg, MSG_NULL, Ordering::Relaxed, Ordering::Relaxed)
        .is_err()
    {
        core::hint::spin_loop();
    }
}

/// CPUX receives a message from CPU0.
#[inline(always)]
fn cpu_x_get_tx() -> i64 {
    loop {
        match CHANNEL_CPU0_TX.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |x| {
            if x != MSG_NULL {
                Some(MSG_NULL)
            } else {
                None
            }
        }) {
            Ok(x) => return x,
            Err(_) => core::hint::spin_loop(),
        }
    }
}

/// CPU0 receives a message from CPUX.
#[inline(always)]
fn cpu_0_get_rx() -> i64 {
    loop {
        match CHANNEL_CPU0_RX.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |x| {
            if x != MSG_NULL {
                Some(MSG_NULL)
            } else {
                None
            }
        }) {
            Ok(x) => return x,
            Err(_) => core::hint::spin_loop(),
        }
    }
}
