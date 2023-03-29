//! This module defines the x86_64's entry point.
//!
//! `kernel_main()` function is the entry point and called by `bootloader` crate.

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
    config::{BACKUP_HEAP_SIZE, HEAP_START, PAGE_SIZE, STACK_SIZE},
    kernel_info::KernelInfo,
};
use alloc::boxed::Box;
use awkernel_lib::delay::{wait_forever, wait_microsec};
use bootloader_api::{
    config::Mapping, entry_point, info::MemoryRegionKind, BootInfo, BootloaderConfig,
};
use core::{
    arch::asm,
    ptr::{read_volatile, write_volatile},
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

// Set `kernel_main` as the entry point.
entry_point!(kernel_main, config = &BOOTLOADER_CONFIG);

/// The entry point of x86_64.
///
/// 1. Enable FPU.
/// 2. Initialize a serial port.
/// 3. Initialize the virtual memory.
/// 4. Initialize the heap memory allocator.
/// 5. Initialize the logger.
/// 6. Initialize interrupt handlers.
/// 7. Initialize ACPI.
/// 8. Initialize stack memory regions for non-primary CPUs.
/// 9. Initialize `awkernel_lib`.
/// 10. Initialize APIC.
/// 11. Boot non-primary CPUs.
/// 12. Call `crate::main()`.
fn kernel_main(boot_info: &'static mut BootInfo) -> ! {
    enable_fpu(); // 1. Enable SSE.

    super::serial::init(); // 2. Initialize the serial port.
    unsafe { super::puts("The primary CPU is waking up.\n") };

    let mut page_table = if let Some(page_table) = unsafe { get_page_table(boot_info) } {
        page_table
    } else {
        unsafe { super::puts("Physical memory is not mapped.\n") };
        wait_forever();
    };

    // 3. Initialize virtual memory

    // Create a page allocator.
    let mut frames = boot_info
        .memory_regions
        .iter()
        .filter(|m| m.kind == MemoryRegionKind::Usable)
        .flat_map(|m| (m.start..m.end).step_by(PAGE_SIZE as _))
        .map(|addr| PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(addr)));

    let mut usable_pages = 0;
    for _ in frames.clone() {
        usable_pages += 1;
    }

    let mut page_allocator = PageAllocator::new(&mut frames);

    // Get offset address to physical memory.
    let Some(offset) = boot_info.physical_memory_offset.as_ref() else {
        unsafe { super::puts("Failed to get the physical memory offset.\n") };
        wait_forever();
    };
    let offset = *offset;

    // Map a page to wake non-primary CPUs up.
    map_for_boot(NON_PRIMARY_START, &mut page_table, &mut page_allocator);

    // Map heap memory region.
    let num_pages = map_heap(
        &mut page_table,
        &mut page_allocator,
        (usable_pages - (128 * 1024 * 1024) / PAGE_SIZE) as usize,
    );

    let backup_start = HEAP_START as usize;
    let backup_size = BACKUP_HEAP_SIZE as usize;
    let primary_start = (HEAP_START + BACKUP_HEAP_SIZE) as usize;
    let primary_size = num_pages * PAGE_SIZE as usize - BACKUP_HEAP_SIZE as usize;

    // 4. Initialize the heap memory allocator.
    unsafe { awkernel_lib::heap::init(primary_start, primary_size, backup_start, backup_size) }; // Enable heap allocator.

    // Use the backup allocator in kernel.
    unsafe { awkernel_lib::heap::TALLOC.use_backup() };

    // 5. Initialize the logger.
    super::serial::init_logger();

    // 6. Initialize interrupt handlers.
    unsafe { interrupt::init() };

    log::info!("Physical memory offset: {:x}", offset);

    // 7. Initialize ACPI.
    let acpi = if let Some(acpi) = awkernel_lib::arch::x86_64::acpi::create_acpi(boot_info, offset)
    {
        acpi
    } else {
        log::error!("Failed to initialize ACPI.");
        wait_forever();
    };

    // 8. Initialize stack memory regions for non-primary CPUs.
    if map_stack(&acpi, &mut page_table, &mut page_allocator).is_err() {
        log::error!("Failed to map stack memory.");
        wait_forever();
    }

    for region in boot_info.memory_regions.iter() {
        log::debug!("{:?}", region);
    }

    // 9. Initialize `awkernel_lib`.
    awkernel_lib::arch::x86_64::init(&acpi, offset);

    // 10. Initialize APIC.
    if let TypeApic::Xapic(apic) = super::apic::new(offset) {
        log::info!("Waking non-primary CPUs up.");
        // 11. Boot non-primary CPUs.
        start_non_primary_cpus(&apic)
    }

    let kernel_info = KernelInfo {
        info: Some(boot_info),
        cpu_id: 0,
    };

    // 12. Call `crate::main()`.
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

const NON_PRIMARY_START: u64 = 4096; // 4KiB. Entry point of 16-bit mode (protected mode).
const ENTRY32: u64 = NON_PRIMARY_START + 1024; // 5KiB. Entry point of 32-bit mode (long mode).

// 6KiB
const NON_PRIMARY_KERNEL_MAIN: u64 = ENTRY32 + 1024;
const CR3_POS: u64 = NON_PRIMARY_KERNEL_MAIN + 8;

pub(super) fn map_for_boot(
    addr: u64,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator,
) {
    let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE;
    unsafe {
        page_table
            .map_to(
                Page::<Size4KiB>::containing_address(VirtAddr::new(addr)),
                PhysFrame::containing_address(PhysAddr::new(addr)),
                flags,
                page_allocator,
            )
            .unwrap()
            .flush()
    };
}

fn start_non_primary_cpus(apic: &dyn Apic) {
    log::debug!("start_non_primary_cpus()");

    // Calculate address.
    let boot16 = include_bytes!("../../../asm/x86/boot16.img");
    let boot16_phy_addr = VirtAddr::new(NON_PRIMARY_START);

    let entry32 = include_bytes!("../../../asm/x86/entry32.img");
    let entry32_phy_addr = VirtAddr::new(ENTRY32);

    let main_addr = VirtAddr::new(NON_PRIMARY_KERNEL_MAIN);
    let cr3_phy_addr = VirtAddr::new(CR3_POS);

    // Store CR3.
    let mut cr3: u64;
    unsafe { asm!("mov {}, cr3", out(reg) cr3, options(nomem, nostack, preserves_flags)) };

    // Save original data.
    let _original = Box::<[u8; PAGE_SIZE as usize]>::new(unsafe {
        read_volatile::<[u8; PAGE_SIZE as usize]>(boot16_phy_addr.as_ptr())
    });

    unsafe {
        // Write boot16.img.
        write_volatile(boot16_phy_addr.as_mut_ptr(), *boot16);

        // Write entry32.img.
        write_volatile(entry32_phy_addr.as_mut_ptr(), *entry32);

        // Write non_primary_kernel_main.
        write_volatile(main_addr.as_mut_ptr(), non_primary_kernel_main as usize);

        // Write CR3.
        write_volatile(cr3_phy_addr.as_mut_ptr(), cr3 as u32);

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
        (NON_PRIMARY_START >> 12) as u8,
    );

    wait_microsec(200); // Wait 200[us]

    // SIPI
    apic.interrupt(
        0,
        DestinationShorthand::AllExcludingSelf,
        IcrFlags::empty(),
        DeliveryMode::StartUp,
        (NON_PRIMARY_START >> 12) as u8,
    );

    wait_microsec(200); // Wait 200[us]
}

#[inline(never)]
fn non_primary_kernel_main() -> ! {
    let ebx = unsafe { core::arch::x86_64::__cpuid(1).ebx };
    let cpu_id = (ebx >> 24) & 0xff;

    enable_fpu(); // Enable SSE.

    // use backup allocator
    unsafe { awkernel_lib::heap::TALLOC.use_backup() };

    // Initialize interrupt handlers.
    unsafe { interrupt::init() };

    let kernel_info = KernelInfo::<Option<&mut BootInfo>> {
        info: None,
        cpu_id: cpu_id as usize,
    };

    crate::main(kernel_info); // jump to userland

    wait_forever();
}
