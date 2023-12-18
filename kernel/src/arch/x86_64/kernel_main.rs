//! This module defines the x86_64's entry point.
//!
//! `kernel_main()` function is the entry point and called by `bootloader` crate.

use super::{config::DMA_SIZE, heap::map_heap, interrupt_handler};
use crate::{
    arch::{config::DMA_START, x86_64::stack::map_stack},
    config::{BACKUP_HEAP_SIZE, HEAP_START, STACK_SIZE},
    kernel_info::KernelInfo,
};
use acpi::{platform::ProcessorState, AcpiTables};
use alloc::{boxed::Box, collections::BTreeMap, vec::Vec};
use awkernel_drivers::interrupt_controller::apic::{
    registers::{DeliveryMode, DestinationShorthand, IcrFlags},
    Apic, TypeApic,
};
use awkernel_lib::{
    arch::x86_64::{
        acpi::AcpiMapper,
        page_allocator::{self, get_page_table, PageAllocator, VecPageAllocator},
        page_table,
    },
    console::unsafe_puts,
    delay::{wait_forever, wait_microsec},
    interrupt::register_interrupt_controller,
    paging::PAGESIZE,
};
use bootloader_api::{
    config::Mapping,
    entry_point,
    info::{MemoryRegion, MemoryRegionKind},
    BootInfo, BootloaderConfig,
};
use core::{
    arch::asm,
    ptr::{read_volatile, write_volatile},
    sync::atomic::{fence, AtomicBool, AtomicUsize, Ordering},
};
use x86_64::{
    registers::control::{Cr0, Cr0Flags, Cr4, Cr4Flags},
    structures::paging::{
        FrameAllocator, Mapper, OffsetPageTable, Page, PageTableFlags, PhysFrame, Size4KiB,
    },
    PhysAddr, VirtAddr,
};

extern "C" {
    static __eh_frame: u64;
}

pub static BOOTLOADER_CONFIG: BootloaderConfig = {
    let mut config = BootloaderConfig::new_default();
    config.mappings.physical_memory = Some(Mapping::Dynamic);
    config.kernel_stack_size = STACK_SIZE as u64;
    config
};

// Set `kernel_main` as the entry point.
entry_point!(kernel_main, config = &BOOTLOADER_CONFIG);

static BSP_READY: AtomicBool = AtomicBool::new(false);
static BOOTED_APS: AtomicUsize = AtomicUsize::new(0);

/// The entry point of x86_64.
///
/// 1. Enable FPU.
/// 2. Initialize a serial port.
/// 3. Initialize the virtual memory.
/// 4. Initialize the backup heap memory allocator.
/// 5. Enable logger.
/// 6. Initialize ACPI.
/// 7. Initialize stack memory regions for non-primary CPUs.
/// 8. Initialize `awkernel_lib`.
/// 9. Initialize APIC.
/// 10. Write boot images to wake non-primary CPUs up.
/// 11. Boot non-primary CPUs.
/// 12. Initialize PCIe devices.
/// 13. Initialize the primary heap memory allocator.
/// 14. Initialize interrupt handlers.
/// 15. Call `crate::main()`.
fn kernel_main(boot_info: &'static mut BootInfo) -> ! {
    enable_fpu(); // 1. Enable SSE.

    super::console::init_device(); // 2. Initialize the serial port.

    unsafe { unsafe_puts("\r\nThe primary CPU is waking up.\r\n") };

    // 3. Initialize virtual memory

    unsafe { page_allocator::init(boot_info) };
    let mut page_table = if let Some(page_table) = unsafe { get_page_table() } {
        page_table
    } else {
        unsafe { unsafe_puts("Physical memory is not mapped.\r\n") };
        wait_forever();
    };

    // Map the page #0.
    map_page0(boot_info, &mut page_table);

    // 4. Initialize the backup heap memory allocator.
    let (backup_pages, backup_region, backup_next_frame) =
        init_backup_heap(boot_info, &mut page_table);

    // 5. Enable logger.
    super::console::register_console();

    log::info!(
        "Backup heap: start = 0x{:x}, size = {}",
        HEAP_START,
        backup_pages * PAGESIZE
    );

    // Get offset address to physical memory.
    let Some(offset) = boot_info.physical_memory_offset.as_ref() else {
        unsafe { unsafe_puts("Failed to get the physical memory offset.\r\n") };
        wait_forever();
    };
    let offset = *offset;

    log::info!("Physical memory offset: 0x{:x}", offset);

    // 6. Initialize ACPI.
    let acpi = if let Some(acpi) = awkernel_lib::arch::x86_64::acpi::create_acpi(boot_info, offset)
    {
        acpi
    } else {
        log::error!("Failed to initialize ACPI.");
        wait_forever();
    };

    // Get NUMA information.
    let (mut numa_to_mem, cpu_to_numa) =
        get_numa_info(boot_info, &acpi, &backup_region, backup_next_frame);

    let mut page_allocators = BTreeMap::new();

    for numa_id in numa_to_mem.keys() {
        let mut page_allocator = init_dma(*numa_id, &mut numa_to_mem, &mut page_table);
        page_allocators.insert(*numa_id, page_allocator);
    }

    // let mut numa_frames = BTreeMap::new();

    // for (numa_id, regions) in numa_to_mem.iter() {
    //     let frames = boot_info
    //         .memory_regions
    //         .iter()
    //         .filter(|m| m.kind == MemoryRegionKind::Usable && m.start != 0)
    //         .flat_map(|m| (m.start..m.end).step_by(PAGESIZE as _))
    //         .map(|addr| PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(addr)));
    //     numa_frames.insert(*numa_id, frames);
    // }

    // // Create a page allocator.
    // let mut frames = boot_info
    //     .memory_regions
    //     .iter()
    //     .filter(|m| m.kind == MemoryRegionKind::Usable && m.start != 0)
    //     .flat_map(|m| {
    //         if m.start != backup_region.start {
    //             m.start..m.end
    //         } else if let Some(frame) = backup_next_frame {
    //             frame.start_address().as_u64()..m.end
    //         } else {
    //             0..0
    //         }
    //         .step_by(PAGESIZE as _)
    //     })
    //     .map(|addr| PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(addr)));

    // let mut page_allocator = PageAllocator::new(&mut frames);

    // 7. Initialize stack memory regions for non-primary CPUs.
    if map_stack(&acpi, &cpu_to_numa, &mut page_table, &mut page_allocators).is_err() {
        log::error!("Failed to map stack memory.");
        wait_forever();
    }

    // 8. Initialize `awkernel_lib` and `awkernel_driver`
    let mut awkernel_page_table = page_table::PageTable::new(&mut page_table);
    awkernel_lib::arch::x86_64::init(&acpi, &mut awkernel_page_table, &mut page_allocators);

    // 9. Initialize APIC.
    let type_apic = awkernel_drivers::interrupt_controller::apic::new(
        &mut awkernel_page_table,
        &mut page_allocators,
    );

    // 10. Write boot images to wake non-primary CPUs up.
    write_boot_images(offset);

    // 11. Boot non-primary CPUs.
    log::info!("Waking non-primary CPUs up.");

    let apic_result = match type_apic {
        TypeApic::Xapic(xapic) => {
            let result = wake_non_primary_cpus(&xapic, &acpi, offset);

            // Register interrupt controller.
            register_interrupt_controller(Box::new(xapic));

            result
        }
        TypeApic::X2Apic(x2apic) => {
            let result = wake_non_primary_cpus(&x2apic, &acpi, offset);

            // Register interrupt controller.
            register_interrupt_controller(Box::new(x2apic));

            result
        }
        _ => {
            log::error!("Failed to initialize APIC.");
            wait_forever();
        }
    };

    if let Err(e) = apic_result {
        log::error!("Failed to initialize APIC. {}", e);
        wait_forever();
    }

    // 12. Initialize PCIe devices.
    awkernel_drivers::pcie::init_with_acpi(
        DMA_START,
        &acpi,
        &mut awkernel_page_table,
        &mut page_allocator,
    );

    // 13. Initialize the primary heap memory allocator.
    init_primary_heap(&mut page_table, &mut page_allocator);

    BSP_READY.store(true, Ordering::Release);

    while BOOTED_APS.load(Ordering::Relaxed) != 0 {
        core::hint::spin_loop();
    }

    // 14. Initialize interrupt handlers.
    unsafe { interrupt_handler::init() };

    let kernel_info = KernelInfo {
        info: Some(boot_info),
        cpu_id: 0,
    };

    // 15. Call `crate::main()`.
    crate::main(kernel_info);

    wait_forever()
}

fn init_primary_heap<T>(
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator<T>,
) where
    T: Iterator<Item = PhysFrame> + Send,
{
    let primary_start = HEAP_START + BACKUP_HEAP_SIZE;
    let primary_size = 1 << 48; // up to 256TiB

    let num_pages = map_heap(page_table, page_allocator, primary_start, primary_size);

    let heap_size = num_pages * PAGESIZE;
    unsafe { awkernel_lib::heap::init_primary(primary_start, heap_size) };

    log::info!(
        "Primary heap: start = 0x{:x}, size = {}",
        primary_start,
        heap_size
    );
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

const NON_PRIMARY_START: u64 = 0; // Entry point of 16-bit mode (protected mode).
const NON_PRIMARY_KERNEL_MAIN: u64 = 2048;
const CR3_POS: u64 = NON_PRIMARY_KERNEL_MAIN + 8;
const FLAG_POS: u64 = CR3_POS + 8;

fn write_boot_images(offset: u64) {
    // Calculate address.
    let mpboot = include_bytes!("../../../asm/x86/mpboot.img");
    let mpboot_phy_addr = VirtAddr::new(NON_PRIMARY_START + offset);

    let main_addr = VirtAddr::new(NON_PRIMARY_KERNEL_MAIN + offset);
    let cr3_phy_addr = VirtAddr::new(CR3_POS + offset);

    // Store CR3.
    let mut cr3: u64;
    unsafe { asm!("mov {}, cr3", out(reg) cr3, options(nomem, nostack, preserves_flags)) };

    unsafe {
        // Write mpboot.img.
        log::info!("write mpboot.img to 0x{mpboot_phy_addr:08x}");
        write_volatile(mpboot_phy_addr.as_mut_ptr(), *mpboot);

        // Write non_primary_kernel_main.
        log::info!(
            "write the kernel entry of 0x{:08x} to 0x{main_addr:08x}",
            non_primary_kernel_main as usize
        );
        write_volatile(main_addr.as_mut_ptr(), non_primary_kernel_main as usize);

        // Write CR3.
        log::info!("write CR3 of 0x{cr3:08x} to 0x{cr3_phy_addr:08x}");
        write_volatile(cr3_phy_addr.as_mut_ptr(), cr3);

        asm!(
            "wbinvd
             mfence"
        );
    }
}

fn wake_non_primary_cpus(
    apic: &dyn Apic,
    acpi: &AcpiTables<AcpiMapper>,
    offset: u64,
) -> Result<(), &'static str> {
    let processor_info = if let Ok(platform_info) = acpi.platform_info() {
        if let Some(processor_info) = platform_info.processor_info {
            processor_info
        } else {
            return Err("Failed processor_info().");
        }
    } else {
        return Err("Failed platform_info().");
    };

    let num_aps = processor_info
        .application_processors
        .iter()
        .fold(0, |acc, p| {
            if matches!(p.state, ProcessorState::WaitingForSipi) {
                acc + 1
            } else {
                acc
            }
        });

    BOOTED_APS.store(num_aps, Ordering::Release);

    for ap in processor_info.application_processors.iter() {
        if matches!(ap.state, ProcessorState::WaitingForSipi) {
            send_ipi(apic, ap.local_apic_id, offset);
        }
    }

    Ok(())
}

fn send_ipi(apic: &dyn Apic, apic_id: u32, offset: u64) {
    let flag_addr = VirtAddr::new(FLAG_POS + offset);
    unsafe { write_volatile::<u64>(flag_addr.as_mut_ptr(), 0) };

    // INIT IPI, ASSERT
    apic.interrupt(
        apic_id,
        DestinationShorthand::NoShorthand,
        IcrFlags::ASSERT | IcrFlags::LEVEL_TRIGGER,
        DeliveryMode::Init,
        0,
    );

    wait_microsec(10_000); // Wait 10[ms]

    // INIT IPI, DEASSERT
    apic.interrupt(
        apic_id,
        DestinationShorthand::NoShorthand,
        IcrFlags::LEVEL_TRIGGER,
        DeliveryMode::Init,
        0,
    );

    wait_microsec(10_000); // Wait 10[ms]

    // SIPI
    apic.interrupt(
        apic_id,
        DestinationShorthand::NoShorthand,
        IcrFlags::ASSERT,
        DeliveryMode::StartUp,
        (NON_PRIMARY_START >> 12) as u8,
    );

    wait_microsec(200); // Wait 200[us]

    unsafe {
        if read_volatile::<u64>(flag_addr.as_ptr()) != 0 {
            return;
        }
    }

    // SIPI
    apic.interrupt(
        apic_id,
        DestinationShorthand::NoShorthand,
        IcrFlags::ASSERT,
        DeliveryMode::StartUp,
        (NON_PRIMARY_START >> 12) as u8,
    );

    wait_microsec(200); // Wait 200[us]
}

#[inline(never)]
fn non_primary_kernel_main() -> ! {
    let ebx = unsafe { core::arch::x86_64::__cpuid(1).ebx };
    let cpu_id = (ebx >> 24) & 0xff;

    while !BSP_READY.load(Ordering::Relaxed) {
        core::hint::spin_loop();
    }
    fence(Ordering::Acquire);

    enable_fpu(); // Enable SSE.

    unsafe { interrupt_handler::load() };

    // use the primary and backup allocator
    unsafe { awkernel_lib::heap::TALLOC.use_primary_then_backup() };

    BOOTED_APS.fetch_sub(1, Ordering::Relaxed);

    let kernel_info = KernelInfo::<Option<&mut BootInfo>> {
        info: None,
        cpu_id: cpu_id as usize,
    };

    crate::main(kernel_info); // jump to userland

    wait_forever();
}

fn map_page0(boot_info: &mut BootInfo, page_table: &mut OffsetPageTable<'static>) {
    let mut page0 = None;
    for region in boot_info.memory_regions.iter() {
        if region.kind == MemoryRegionKind::Usable && region.start == 0 {
            page0 = Some(region.clone());
            break;
        }
    }

    if let Some(_) = page0 {
        unsafe { unsafe_puts("The page #0 is not available.\r\n") };
        wait_forever();
    };

    let mut frames = (0..PAGESIZE as u64)
        .step_by(PAGESIZE as _)
        .map(|addr| PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(addr)));

    let mut page_allocator = PageAllocator::new(&mut frames);

    unsafe {
        match page_table.map_to(
            Page::containing_address(VirtAddr::new(0)),
            PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(0)),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
            &mut page_allocator,
        ) {
            Ok(f) => f.flush(),
            Err(_) => {
                unsafe_puts("Failed to map the page #0.\r\n");
                wait_forever();
            }
        }
    }
}

fn init_backup_heap(
    boot_info: &mut BootInfo,
    page_table: &mut OffsetPageTable<'static>,
) -> (usize, MemoryRegion, Option<PhysFrame>) {
    let mut backup_heap_region = None;
    for region in boot_info.memory_regions.iter() {
        if region.kind == MemoryRegionKind::Usable
            && region.end - region.start > BACKUP_HEAP_SIZE as u64 * 2
        {
            backup_heap_region = Some(region.clone());
            break;
        }
    }

    let Some(backup_heap_region) = backup_heap_region else {
        unsafe { unsafe_puts("Failed to find a backup heap memory region.\r\n") };
        wait_forever();
    };

    let mut frames = (backup_heap_region.start..backup_heap_region.end)
        .step_by(PAGESIZE as _)
        .map(|addr| PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(addr)));

    let mut page_allocator = PageAllocator::new(&mut frames);

    let backup_pages = map_heap(
        page_table,
        &mut page_allocator,
        HEAP_START,
        BACKUP_HEAP_SIZE,
    );

    let next_page = page_allocator.allocate_frame();

    // Initialize.
    // Enable heap allocator.
    unsafe {
        awkernel_lib::heap::init_backup(HEAP_START, BACKUP_HEAP_SIZE);
        awkernel_lib::heap::TALLOC.use_primary_then_backup()
    };

    (backup_pages, backup_heap_region, next_page)
}

/// Get NUMA information from ACPI.
/// Return a map from NUMA ID to memory region and a map from CPU ID to NUMA ID.
fn get_numa_info(
    boot_info: &mut BootInfo,
    acpi: &AcpiTables<AcpiMapper>,
    backup_region: &MemoryRegion,
    backup_next_frame: Option<PhysFrame>,
) -> (BTreeMap<u32, Vec<MemoryRegion>>, BTreeMap<u32, u32>) {
    let mut numa_id_to_memory = BTreeMap::new();
    let mut cpu_to_numa_id = BTreeMap::new();

    if let Ok(srat) = acpi.find_table::<awkernel_lib::arch::x86_64::acpi::srat::Srat>() {
        for entry in srat.entries() {
            // log::info!("SRAT entry: {:?}", entry);
            match entry {
                awkernel_lib::arch::x86_64::acpi::srat::SratEntry::MemoryAffinity(affinity) => {
                    let start = affinity.lo_base as usize | ((affinity.hi_base as usize) << 32);
                    let length =
                        affinity.lo_length as usize | ((affinity.hi_length as usize) << 32);

                    numa_id_to_memory.insert(affinity.domain, (start, length));
                }
                awkernel_lib::arch::x86_64::acpi::srat::SratEntry::LocalApic(srat_apic) => {
                    let domain = srat_apic.lo_dm as u32
                        | ((srat_apic.hi_dm[0] as u32) << 8)
                        | ((srat_apic.hi_dm[1] as u32) << 16)
                        | ((srat_apic.hi_dm[2] as u32) << 24);
                    cpu_to_numa_id.insert(srat_apic.apic_id as u32, domain);
                }
                awkernel_lib::arch::x86_64::acpi::srat::SratEntry::LocalX2Apic(srat_apic) => {
                    let domain = srat_apic.domain;
                    cpu_to_numa_id.insert(srat_apic.x2apic_id, domain);
                }
                _ => (),
            }
        }
    } else {
        log::error!("Failed to find SRAT.");
        wait_forever();
    }

    let mut memory_regions = BTreeMap::new();

    for region in boot_info
        .memory_regions
        .iter()
        .filter(|m| m.kind == MemoryRegionKind::Usable && m.start != 0)
    {
        for (numa_id, (start, length)) in numa_id_to_memory.iter() {
            if *start <= region.start as usize && region.end as usize <= *start + *length {
                log::info!(
                    "Memory region 0x{:x} - 0x{:x} is in NUMA node {}",
                    region.start,
                    region.end,
                    numa_id
                );

                let new_region = if region.start != backup_region.start {
                    // Exclude the backup heap memory region.
                    region.clone()
                } else if region.start == 0 {
                    // Exclude the page #0.
                    continue;
                } else if let Some(frame) = backup_next_frame {
                    MemoryRegion {
                        start: frame.start_address().as_u64(),
                        end: region.end,
                        kind: MemoryRegionKind::Usable,
                    }
                } else {
                    MemoryRegion::empty()
                };

                memory_regions
                    .entry(*numa_id)
                    .or_insert_with(|| Vec::new())
                    .push(new_region);

                break;
            }
        }
    }

    (memory_regions, cpu_to_numa_id)
}

fn init_dma(
    numa_id: u32,
    numa_memory: &mut BTreeMap<u32, Vec<MemoryRegion>>,
    page_table: &mut OffsetPageTable<'static>,
) -> VecPageAllocator {
    let mut dma_region = None;

    let Some(mut numa_memory) = numa_memory.remove(&numa_id) else {
        log::error!("Failed to get NUMA memory. NUMA ID = {}", numa_id);
        awkernel_lib::delay::wait_forever();
    };

    for region in numa_memory.iter_mut() {
        if region.end - region.start >= DMA_SIZE as u64 {
            dma_region = Some(MemoryRegion {
                start: region.start,
                end: region.start + DMA_SIZE as u64,
                kind: MemoryRegionKind::Usable,
            });

            region.start = region.start + DMA_SIZE as u64;

            break;
        }
    }

    let Some(dma_region) = dma_region else {
        log::error!("Failed to allocate a DMA region. NUMA ID = {}", numa_id);
        awkernel_lib::delay::wait_forever();
    };

    let mut page_allocator = page_allocator::VecPageAllocator::new(numa_memory);
    let dma_start = DMA_START + numa_id as usize * DMA_SIZE;
    let dma_end = dma_start + (dma_region.end - dma_region.start) as usize;

    for (i, dma_phy_frame) in (dma_region.start..dma_region.end)
        .step_by(PAGESIZE as _)
        .map(|addr| PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(addr)))
        .enumerate()
    {
        let virt_frame =
            Page::containing_address(VirtAddr::new((dma_start + i * PAGESIZE as usize) as u64));
        let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_CACHE;

        unsafe {
            page_table
                .map_to(virt_frame, dma_phy_frame, flags, &mut page_allocator)
                .unwrap()
                .flush()
        };
    }

    unsafe {
        awkernel_lib::dma_pool::init_dma_pool(
            numa_id as usize,
            awkernel_lib::addr::virt_addr::VirtAddr::new(dma_start),
            (dma_region.end - dma_region.start) as usize,
        )
    };

    page_allocator
}
