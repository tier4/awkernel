use acpi::{platform::PmTimer, AcpiHandler, AcpiTables};
use bootloader_api::BootInfo;
use core::{
    arch::x86_64::_mm_pause,
    ptr::{read_volatile, write_volatile, NonNull},
};
use x86_64::{instructions::port::Port, VirtAddr};

static mut PM_TIMER: Option<PmTimer> = None;

#[derive(Debug, Clone)]
pub struct AcpiMapper {
    phy_offset: VirtAddr,
}

impl AcpiHandler for AcpiMapper {
    unsafe fn map_physical_region<T>(
        &self,
        physical_address: usize,
        size: usize,
    ) -> acpi::PhysicalMapping<Self, T> {
        let addr = self.phy_offset + physical_address;
        let virtual_start = NonNull::new(addr.as_mut_ptr() as *mut T).unwrap();

        acpi::PhysicalMapping::new(physical_address, virtual_start, size, size, self.clone())
    }

    fn unmap_physical_region<T>(_region: &acpi::PhysicalMapping<Self, T>) {}
}

impl AcpiMapper {
    pub fn new(phy_offset: VirtAddr) -> Self {
        Self { phy_offset }
    }
}

pub fn create_acpi(boot_info: &BootInfo, phy_offset: u64) -> Option<AcpiTables<AcpiMapper>> {
    if let Some(rsdp_addr) = boot_info.rsdp_addr.as_ref() {
        match unsafe {
            acpi::AcpiTables::from_rsdp(
                AcpiMapper::new(VirtAddr::new(phy_offset)),
                *rsdp_addr as usize,
            )
        } {
            Ok(acpi) => Some(acpi),
            Err(err) => {
                log::error!("Failed to create AcpiTables: err = {:?}", err);
                None
            }
        }
    } else {
        None
    }
}

pub const ACPI_TMR_HZ: u32 = 3579545;

pub fn init(acpi: &AcpiTables<AcpiMapper>) {
    let Ok(platfomr_info) = acpi.platform_info() else {
        log::error!("Not found platform information.");
        return;
    };

    let Some(pm_timer) = platfomr_info.pm_timer else {
        log::error!("Not found PM Timer.");
        return;
    };

    unsafe { write_volatile(&mut PM_TIMER, Some(pm_timer)) };
}

pub fn wait_usec(usec: u64) {
    let Some(pm_timer) = (unsafe { read_volatile(&PM_TIMER) }) else { return; };

    let mut port = Port::<u32>::new(pm_timer.base.address as u16);

    let max: u64 = if pm_timer.supports_32bit {
        1 << 32 // 32-bit counter
    } else {
        1 << 24 // 24-bit counter
    };

    // Counts per usec.
    let clk = (ACPI_TMR_HZ as u64 * usec) / 1000_000;
    let mut prev = unsafe { port.read() } as u64;
    let mut acc = 0;

    while acc < clk {
        let cur = unsafe { port.read() } as u64;
        acc += if cur < prev {
            // overflow
            max + cur - prev
        } else {
            cur - prev
        };

        prev = cur;
        unsafe { _mm_pause() };
    }
}
