use super::{
    acpi::{wait_usec, AcpiMapper},
    apic::{Apic, TypeApic},
    delay, interrupt,
    page_allocator::PageAllocator,
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
use bootloader_api::{
    config::Mapping, entry_point, info::MemoryRegionKind, BootInfo, BootloaderConfig,
};
use core::{
    arch::asm,
    ptr::{read_volatile, write_volatile},
};
use x86_64::{
    registers::control::{Cr0, Cr0Flags, Cr3, Cr4, Cr4Flags},
    structures::paging::{
        Mapper, OffsetPageTable, Page, PageTable, PageTableFlags, PhysFrame, Size4KiB, Translate,
    },
    PhysAddr, VirtAddr,
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

    // Create a page allocator.
    let mut frames = boot_info
        .memory_regions
        .iter()
        .filter(|m| m.kind == MemoryRegionKind::Usable)
        .flat_map(|m| (m.start..m.end).step_by(4096))
        .map(|addr| PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(addr)));
    let mut page_allocator = PageAllocator::new(&mut frames);

    // Map heap memory region.
    if super::heap::HeapMapper::init(boot_info, &mut page_table, &mut page_allocator).is_err() {
        super::serial::puts("Failed to map heap memory.");
        delay::ArchDelay::wait_forever();
    }

    heap::init(); // Enable heap allocator.
    enable_fpu(); // Enable SSE.
    unsafe { interrupt::init() }; // Initialize interrupt handlers.

    for region in boot_info.memory_regions.into_iter() {
        log::debug!("{:?}", region);
    }

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
        TypeApic::Xapic(apic) => {
            start_non_primary_cpus(&mut page_table, &mut page_allocator, *offset, &apic, &acpi)
        }
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

const NON_PRIMARY_START: u64 = 1024 * 4; // 4KiB
const ENTRY32: u64 = 1024 * 5; // 5KiB
const CR3_POS: u64 = 1024 * 6; // 6KiB

fn start_non_primary_cpus(
    page_table: &mut OffsetPageTable,
    page_allocator: &mut PageAllocator,
    phy_offset: u64,
    apic: &dyn Apic,
    acpi: &AcpiTables<AcpiMapper>,
) {
    // Calculate address.
    let boot16 = include_bytes!("../../../asm/x86/boot16.img");
    let boot16_phy_addr = VirtAddr::new(phy_offset + NON_PRIMARY_START);

    let entry32 = include_bytes!("../../../asm/x86/entry32.img");
    let entry32_phy_addr = VirtAddr::new(phy_offset + ENTRY32);

    let cr3_phy_addr = VirtAddr::new(phy_offset + CR3_POS);

    // Map 2nd page.
    let flags = PageTableFlags::PRESENT | PageTableFlags::NO_CACHE;

    if let Err(e) = unsafe {
        page_table.map_to(
            Page::<Size4KiB>::containing_address(VirtAddr::new(NON_PRIMARY_START)),
            PhysFrame::containing_address(PhysAddr::new(NON_PRIMARY_START)),
            flags,
            page_allocator,
        )
    } {
        log::error!("Failed to map 2nd page: {:?}", e);
    }

    let addr = VirtAddr::new(4096);
    let phy_addr = page_table.translate_addr(addr);
    log::debug!("VirtAddry(0x1000) => {:?}", phy_addr);

    // Store CR3.
    let mut cr3: u64;
    unsafe { asm!("mov {}, cr3", out(reg) cr3, options(nomem, nostack, preserves_flags)) };
    log::debug!("CR3 = {:x}", cr3);

    // Save original data.
    let original =
        Box::<[u8; 4096]>::new(unsafe { read_volatile::<[u8; 4096]>(boot16_phy_addr.as_ptr()) });

    unsafe {
        // Write CR3.
        write_volatile(cr3_phy_addr.as_mut_ptr(), cr3 as u32);

        // Write boot16.img.
        write_volatile(boot16_phy_addr.as_mut_ptr(), *boot16);

        // Write entry32.img.
        write_volatile(entry32_phy_addr.as_mut_ptr(), *entry32);

        asm!("wbinvd");
    }

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
}
