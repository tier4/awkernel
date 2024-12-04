use super::{acpi::AcpiMapper, page_allocator::VecPageAllocator};
use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
    cpu::cpu_id,
    delay::{uptime, wait_forever, wait_microsec, Delay},
    mmio_r, mmio_rw,
    paging::{Flags, PageTable},
    sync::{mcs::MCSNode, mutex::Mutex},
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

static CPU0_TSC: AtomicU64 = AtomicU64::new(0);

const HPET_GENERAL_CONF_ENABLE: u64 = 1;

static LAST_UPTIME: Mutex<u128> = Mutex::new(0);

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
        let result = diff as u128 * 1_000_000_000 / hz;

        let mut node = MCSNode::new();
        let mut last = LAST_UPTIME.lock(&mut node);
        if *last < result {
            *last = result;
            result
        } else {
            *last
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
    log::info!("TSC Frequency = {} Hz", hz);

    unsafe { TSC_FREQ = hz };

    // Initialize TSC counter.
    let counter = read_tsc();
    TSC_COUNTER_START.store(counter, Ordering::Relaxed);
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
fn read_tsc() -> u64 {
    sync::atomic::fence(Ordering::Acquire);
    let now = unsafe { core::arch::x86_64::_rdtsc() };
    sync::atomic::fence(Ordering::Release);

    now
}

const IA32_TIME_STAMP_COUNTER: u32 = 0x10;
const SYNCRHONIZE_TRIES: usize = 11;
static SYNCHRONIZE_CHANNEL: AtomicI64 = AtomicI64::new(0);
static NEXT_CPU: AtomicUsize = AtomicUsize::new(1);

/// Synchronize the TSC.
/// Calculate the offset between the TSC of CPU0 and other CPUs.
///
/// # Safety
///
/// This function must be called during the kernel initialization.
pub unsafe fn synchronize_tsc(num_cpu: usize) {
    let cpu_id = cpu_id();

    if cpu_id == 0 {
        wait_microsec(10000);
        CPU0_TSC.store(read_tsc(), Ordering::Relaxed);
    } else {
        let cpu0_tsc = loop {
            let cpu0_tsc = CPU0_TSC.load(Ordering::Relaxed);
            if cpu0_tsc != 0 {
                break cpu0_tsc;
            }
        };

        // Initialize the TSC counter.
        x86_64::registers::model_specific::Msr::new(IA32_TIME_STAMP_COUNTER).write(cpu0_tsc);
    }

    // Synchronize the TSC counter.
    // This algorithm is based on NTP's synchronization algorithm.
    //
    // - client:
    //   - t0 = time();
    //   - send to server
    // - server:
    //   - receive from client
    //   - t1 = time(); // server receive time
    //   - t2 = time(); // server send time
    //   - send to client
    // - client:
    //   - receive from server
    //   - t3 = time();
    // - offset = ((t1 - t0) + (t2 - t3)) / 2
    if cpu_id == 0 {
        'outer: loop {
            // Receive message
            let t1 = {
                loop {
                    let msg = SYNCHRONIZE_CHANNEL.load(Ordering::Relaxed);
                    if msg == -2 {
                        break 'outer;
                    }

                    if msg != 0 {
                        break;
                    }
                    core::hint::spin_loop();
                }

                // Receive time
                read_tsc() as i64
            };

            // Send time
            let t2 = read_tsc() as i64;

            // Send message
            SYNCHRONIZE_CHANNEL.store(t1 + t2, Ordering::Relaxed);

            // Wait for the next synchronization.
            while SYNCHRONIZE_CHANNEL.load(Ordering::Relaxed) != 0 {
                core::hint::spin_loop();
            }
        }

        log::info!("CPU0: TSC synchronization is done.");
    } else {
        while NEXT_CPU.load(Ordering::Relaxed) != cpu_id {
            core::hint::spin_loop();
        }

        let mut time_offset = [0; SYNCRHONIZE_TRIES];

        for offset in time_offset.iter_mut() {
            // Send message to CPU0.
            let t0 = read_tsc() as i64;
            SYNCHRONIZE_CHANNEL.store(-1, Ordering::Relaxed);

            // Receive message from CPU0.
            let t1_t2 = loop {
                let t1_t2 = SYNCHRONIZE_CHANNEL.load(Ordering::Relaxed);
                if t1_t2 != -1 {
                    break t1_t2;
                }

                core::hint::spin_loop();
            };

            // Receive time
            let t3 = read_tsc() as i64;

            *offset = (t1_t2 - t0 - t3) / 2;

            // Notify end of the synchronization to CPU0.
            SYNCHRONIZE_CHANNEL.store(0, Ordering::Relaxed);

            let n0 = crate::delay::cpu_counter();
            loop {
                let n1 = crate::delay::cpu_counter();
                if n1 - n0 >= 100_000 {
                    break;
                }
            }
        }

        time_offset.sort_unstable();

        let tsc = (read_tsc() as i64 + time_offset[SYNCRHONIZE_TRIES / 2]) as u64;

        // Initialize the TSC counter.
        x86_64::registers::model_specific::Msr::new(IA32_TIME_STAMP_COUNTER).write(tsc);

        // Notify the next CPU.
        NEXT_CPU.fetch_add(1, Ordering::Relaxed);

        if cpu_id == num_cpu - 1 {
            SYNCHRONIZE_CHANNEL.store(-2, Ordering::Relaxed);
        }
    }
}
