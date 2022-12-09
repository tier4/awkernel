use super::{
    acpi::{wait_usec, AcpiMapper},
    apic::{Apic, TypeApic},
    delay, interrupt,
};
use crate::{
    arch::{
        x86_64::apic::{DeliveryMode, DestinationShorthand, IcrFlags},
        Delay,
    },
    heap,
    kernel_info::KernelInfo,
};
use acpi::AcpiTables;
use alloc::boxed::Box;
use bootloader_api::{config::Mapping, entry_point, BootInfo, BootloaderConfig};
use core::{
    arch::asm,
    ptr::{read_volatile, write_volatile},
};
use x86_64::{
    registers::control::{Cr0, Cr0Flags, Cr3, Cr4, Cr4Flags},
    structures::paging::{OffsetPageTable, PageTable},
    VirtAddr,
};

extern "C" {
    static __eh_frame: u64;
}

pub static BOOTLOADER_CONFIG: BootloaderConfig = {
    let mut config = BootloaderConfig::new_default();
    config.mappings.physical_memory = Some(Mapping::Dynamic);
    config.kernel_stack_size = 2 * 1024 * 1024; // 2MiB
    config
};

entry_point!(kernel_main, config = &BOOTLOADER_CONFIG);

fn kernel_main(boot_info: &'static mut BootInfo) -> ! {
    super::serial::init(); // Initialize a serial port and logger.

    let mut page_table = if let Some(page_table) = unsafe { get_page_table(boot_info) } {
        page_table
    } else {
        super::serial::puts("Physical memory is not mapped.");
        delay::ArchDelay::wait_forever();
    };

    // Map heap memory region.
    if super::heap::HeapMapper::init(boot_info, &mut page_table).is_err() {
        super::serial::puts("Failed to map heap memory.");
        delay::ArchDelay::wait_forever();
    }

    heap::init(); // Enable heap allocator.
    enable_fpu(); // Enable SSE.
    unsafe { interrupt::init() }; // Initialize interrupt handlers.

    // Get offset address to physical memory.
    let offset = if let Some(offset) = boot_info.physical_memory_offset.as_ref() {
        log::info!("Physical memory offset = {:x}", offset);
        offset
    } else {
        log::error!("Failed to get physical memory offset.");
        delay::ArchDelay::wait_forever();
    };

    // Get ACPI tables.
    let acpi = if let Some(acpi) = super::acpi::create_acpi(boot_info, *offset) {
        acpi
    } else {
        log::error!("Failed to initialize ACPI.");
        delay::ArchDelay::wait_forever();
    };

    // Initialize APIC.
    match super::apic::new(*offset) {
        TypeApic::Xapic(apic) => start_non_primary_cpus(&page_table, *offset, &apic, &acpi),
        _ => (),
    }

    let kernel_info = KernelInfo {
        info: boot_info,
        cpu_id: 0,
    };

    crate::main(kernel_info);

    super::delay::ArchDelay::wait_forever();
}

fn enable_fpu() {
    let mut cr0flags = Cr0::read();
    cr0flags &= !Cr0Flags::EMULATE_COPROCESSOR;
    cr0flags |= Cr0Flags::MONITOR_COPROCESSOR;

    unsafe { Cr0::write(cr0flags) };

    let mut cr4flags = Cr4::read();
    cr4flags |= Cr4Flags::OSFXSR | Cr4Flags::OSXMMEXCPT_ENABLE;

    unsafe { Cr4::write(cr4flags) };
}

unsafe fn get_page_table(boot_info: &BootInfo) -> Option<OffsetPageTable<'static>> {
    let physical_memory_offset = VirtAddr::new(*boot_info.physical_memory_offset.as_ref()?);

    let level_4_table = active_level_4_table(physical_memory_offset);
    Some(OffsetPageTable::new(level_4_table, physical_memory_offset))
}

unsafe fn active_level_4_table(physical_memory_offset: VirtAddr) -> &'static mut PageTable {
    let (level_4_table_frame, _) = Cr3::read();

    let phys = level_4_table_frame.start_address();
    let virt = physical_memory_offset + phys.as_u64();
    let ptr = virt.as_mut_ptr() as *mut PageTable;

    &mut *ptr
}

const NON_PRIMARY_START: u64 = 0x1000;

fn start_non_primary_cpus(
    page_table: &OffsetPageTable,
    phy_offset: u64,
    apic: &dyn Apic,
    acpi: &AcpiTables<AcpiMapper>,
) {
    let boot16 = include_bytes!("../../../asm/x86/boot16.img");
    let boot16_phy_addr = VirtAddr::new(phy_offset + NON_PRIMARY_START);

    let original =
        Box::<[u8; 4096]>::new(unsafe { read_volatile::<[u8; 4096]>(boot16_phy_addr.as_ptr()) });

    // Write boot16.img to the 2nd page (4096..=8192).
    unsafe { write_volatile(boot16_phy_addr.as_mut_ptr(), *boot16) };

    let data_addr = VirtAddr::new(phy_offset + NON_PRIMARY_START + 1024);
    let data = unsafe { read_volatile::<u32>(data_addr.as_ptr()) };
    log::debug!("data = {data}");

    unsafe { asm!("wbinvd") };

    // INIT IPI
    apic.interrupt(
        0,
        DestinationShorthand::AllExcludingSelf,
        IcrFlags::DESTINATION_LOGICAL,
        DeliveryMode::Init,
        0,
    );

    wait_usec(10_000, acpi); // Wait 10[ms]

    // SIPI
    apic.interrupt(
        0,
        DestinationShorthand::AllExcludingSelf,
        IcrFlags::DESTINATION_LOGICAL,
        DeliveryMode::StartUp,
        (NON_PRIMARY_START >> 12) as u8, // 2nd Page
    );

    wait_usec(200, acpi); // Wait 200[us]

    // SIPI
    apic.interrupt(
        0,
        DestinationShorthand::AllExcludingSelf,
        IcrFlags::empty(),
        DeliveryMode::StartUp,
        (NON_PRIMARY_START >> 12) as u8, // 2nd Page
    );

    wait_usec(200, acpi); // Wait 200[us]

    let data = unsafe { read_volatile::<u32>(data_addr.as_ptr()) };
    log::debug!("data = {data}");
}
