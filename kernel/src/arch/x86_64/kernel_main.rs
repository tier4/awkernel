use super::{
    apic::{Apic, TypeApic},
    heap::map_heap,
    interrupt,
    page_allocator::{get_page_table, PageAllocator},
};
use crate::{
    arch::x86_64::{
        apic::{DeliveryMode, DestinationShorthand, IcrFlags},
        stack::map_stack,
    },
    config::{PAGE_SIZE, STACK_SIZE},
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
use t4os_lib::{
    arch::x86_64::acpi::AcpiMapper,
    delay::{wait_forever, wait_microsec},
};
use x86_64::{
    registers::control::{Cr0, Cr0Flags, Cr4, Cr4Flags},
    structures::paging::{Mapper, OffsetPageTable, Page, PageTableFlags, PhysFrame, Size4KiB},
    PhysAddr, VirtAddr,
};

extern "C" {
    static __eh_frame: u64;
}

pub static BOOTLOADER_CONFIG: BootloaderConfig = {
    let mut config = BootloaderConfig::new_default();
    config.mappings.physical_memory = Some(Mapping::Dynamic);
    config.kernel_stack_size = STACK_SIZE;
    config
};

entry_point!(kernel_main, config = &BOOTLOADER_CONFIG);

fn kernel_main(boot_info: &'static mut BootInfo) -> ! {
    enable_fpu(); // Enable SSE.

    super::serial::init(); // Initialize the serial port.
    unsafe { super::puts("The primary CPU is waking up.\n") };

    let mut page_table = if let Some(page_table) = unsafe { get_page_table(boot_info) } {
        page_table
    } else {
        unsafe { super::puts("Physical memory is not mapped.\n") };
        wait_forever();
    };

    // Create a page allocator.
    let mut frames = boot_info
        .memory_regions
        .iter()
        .filter(|m| m.kind == MemoryRegionKind::Usable)
        .flat_map(|m| (m.start..m.end).step_by(PAGE_SIZE as _))
        .map(|addr| PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(addr)));
    let mut page_allocator = PageAllocator::new(&mut frames);

    // Map heap memory region.
    if map_heap(&mut page_table, &mut page_allocator).is_err() {
        unsafe { super::puts("Failed to map heap memory.\n") };
        wait_forever();
    }

    crate::heap::init(); // Enable heap allocator.
    unsafe { interrupt::init() }; // Initialize interrupt handlers.
    super::serial::init_logger(); // Initialize logger.

    for region in boot_info.memory_regions.into_iter() {
        log::debug!("{:?}", region);
    }

    // Get offset address to physical memory.
    let offset = if let Some(offset) = boot_info.physical_memory_offset.as_ref() {
        log::info!("Physical memory offset = 0x{:x}", offset);
        *offset
    } else {
        log::error!("Failed to get physical memory offset.");
        wait_forever();
    };

    // Get ACPI tables.
    let acpi = if let Some(acpi) = t4os_lib::arch::x86_64::acpi::create_acpi(boot_info, offset) {
        acpi
    } else {
        log::error!("Failed to initialize ACPI.");
        wait_forever();
    };

    // Initialize.
    t4os_lib::arch::x86_64::init(&acpi, offset);

    // Initialize APIC.
    match super::apic::new(offset) {
        TypeApic::Xapic(apic) => {
            start_non_primary_cpus(&mut page_table, &mut page_allocator, offset, &apic, &acpi)
        }
        _ => (),
    }

    let kernel_info = KernelInfo {
        info: Some(boot_info),
        cpu_id: 0,
    };

    crate::main(kernel_info);

    wait_forever()
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

const NON_PRIMARY_START: u64 = 1024 * 4; // 4KiB
const ENTRY32: u64 = 1024 * 5; // 5KiB

// 6KiB
const NON_PRIMARY_KERNEL_MAIN: u64 = 1024 * 6;
const CR3_POS: u64 = 1024 * 6 + 8;

fn start_non_primary_cpus(
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator,
    phy_offset: u64,
    apic: &dyn Apic,
    acpi: &AcpiTables<AcpiMapper>,
) {
    // Map stack memory.
    if map_stack(acpi, page_table, page_allocator).is_err() {
        return;
    }

    // Calculate address.
    let boot16 = include_bytes!("../../../asm/x86/boot16.img");
    let boot16_phy_addr = VirtAddr::new(phy_offset + NON_PRIMARY_START);

    let entry32 = include_bytes!("../../../asm/x86/entry32.img");
    let entry32_phy_addr = VirtAddr::new(phy_offset + ENTRY32);

    let main_addr = VirtAddr::new(phy_offset + NON_PRIMARY_KERNEL_MAIN);
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

    // Store CR3.
    let mut cr3: u64;
    unsafe { asm!("mov {}, cr3", out(reg) cr3, options(nomem, nostack, preserves_flags)) };

    // Save original data.
    let _original = Box::<[u8; PAGE_SIZE as usize]>::new(unsafe {
        read_volatile::<[u8; PAGE_SIZE as usize]>(boot16_phy_addr.as_ptr())
    });

    unsafe {
        // Write non_primary_kernel_main.
        write_volatile(main_addr.as_mut_ptr(), non_primary_kernel_main as u64);

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

    wait_microsec(10_000); // Wait 10[ms]

    // SIPI
    apic.interrupt(
        0,
        DestinationShorthand::AllExcludingSelf,
        IcrFlags::DESTINATION_LOGICAL,
        DeliveryMode::StartUp,
        (NON_PRIMARY_START >> 12) as u8, // 2nd Page
    );

    wait_microsec(200); // Wait 200[us]

    // SIPI
    apic.interrupt(
        0,
        DestinationShorthand::AllExcludingSelf,
        IcrFlags::empty(),
        DeliveryMode::StartUp,
        (NON_PRIMARY_START >> 12) as u8, // 2nd Page
    );

    wait_microsec(200); // Wait 200[us]
}

#[inline(never)]
fn non_primary_kernel_main() -> ! {
    let ebx = unsafe { core::arch::x86_64::__cpuid(1).ebx };
    let cpu_id = (ebx >> 24) & 0xff;

    enable_fpu(); // Enable SSE.
    unsafe { interrupt::init() }; // Initialize interrupt handlers.

    let kernel_info = KernelInfo::<Option<&mut BootInfo>> {
        info: None,
        cpu_id: cpu_id as usize,
    };

    crate::main(kernel_info);

    wait_forever();
}
