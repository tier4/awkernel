//! This module defines the x86_64's entry point.
//!
//! `kernel_main()` function is the entry point and called by `bootloader` crate.

use super::{
    heap::{map_backup_heap, map_primary_heap},
    interrupt_handler,
};
use crate::{
    arch::{config::DMA_START, x86_64::stack::map_stack},
    config::{BACKUP_HEAP_SIZE, DMA_SIZE, HEAP_START, STACK_SIZE},
    kernel_info::KernelInfo,
};
use acpi::{platform::ProcessorState, AcpiTables};
use alloc::{
    boxed::Box,
    collections::{btree_set::BTreeSet, BTreeMap, VecDeque},
    vec::Vec,
};
use awkernel_drivers::interrupt_controller::apic::{
    registers::{DeliveryMode, DestinationShorthand, IcrFlags},
    Apic, TypeApic,
};
use awkernel_lib::{
    arch::x86_64::{
        acpi::AcpiMapper,
        cpu::set_raw_cpu_id_to_numa,
        delay::synchronize_tsc,
        interrupt_remap::init_interrupt_remap,
        page_allocator::{self, get_page_table, PageAllocator, VecPageAllocator},
        page_table,
    },
    console::{self, unsafe_puts},
    delay::{wait_forever, wait_microsec},
    interrupt::register_interrupt_controller,
    paging::{PageTable, PAGESIZE},
    unwind::catch_unwind,
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
static NUM_CPUS: AtomicUsize = AtomicUsize::new(0);

const MPBOOT_REGION_END: u64 = 1024 * 1024;

/// The entry point of x86_64.
///
/// 0. Initialize the configuration.
/// 1. Enable FPU.
/// 2. Initialize a serial port.
/// 3. Initialize the virtual memory.
/// 4. Initialize the backup heap memory allocator.
/// 5. Enable logger.
/// 6. Get offset address to physical memory.
/// 7. Initialize ACPI.
/// 8. Get NUMA information.
/// 9. Initialize stack memory regions for non-primary CPUs.
/// 10. Initialize `awkernel_lib`.
/// 11. Initialize APIC.
/// 12. Map a page for `mpboot.img`.
/// 13. Write boot images to wake non-primary CPUs up.
/// 14. Boot non-primary CPUs.
/// 15. Initialize the primary heap memory allocator.
/// 16. Initialize PCIe devices.
/// 17. Initialize interrupt handlers.
/// 18. Synchronize TSC.
/// 19. Call `crate::main()`.
fn kernel_main(boot_info: &'static mut BootInfo) -> ! {
    unsafe { crate::config::init() }; // 0. Initialize the configuration.

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

    // 4. Initialize the backup heap memory allocator.
    let (backup_pages, backup_region, backup_next_frame) =
        init_backup_heap(boot_info, &mut page_table);

    let _ = catch_unwind(|| {
        kernel_main2(
            boot_info,
            page_table,
            backup_pages,
            backup_region,
            backup_next_frame,
        )
    });

    wait_forever();
}

fn kernel_main2(
    boot_info: &'static mut BootInfo,
    mut page_table: OffsetPageTable<'static>,
    backup_pages: usize,
    backup_region: MemoryRegion,
    backup_next_frame: Option<PhysFrame>,
) {
    // 5. Enable logger.
    unsafe { awkernel_lib::logger::init() };
    super::console::register_console();

    log::info!(
        "Backup heap: start = 0x{:x}, size = {}MiB",
        HEAP_START,
        backup_pages * PAGESIZE / 1024 / 1024
    );

    // 6. Get offset address to physical memory.
    let Some(offset) = boot_info.physical_memory_offset.as_ref() else {
        unsafe { unsafe_puts("Failed to get the physical memory offset.\r\n") };
        wait_forever();
    };
    let offset = *offset;

    log::info!("Physical memory offset: 0x{:x}", offset);

    // 7. Initialize ACPI.
    let acpi = if let Some(acpi) = awkernel_lib::arch::x86_64::acpi::create_acpi(boot_info, offset)
    {
        acpi
    } else {
        log::error!("Failed to initialize ACPI.");
        wait_forever();
    };

    // 8. Get NUMA information.
    let (mut numa_to_mem, cpu_to_numa) =
        get_numa_info(boot_info, &acpi, &backup_region, backup_next_frame);

    let mut page_allocators = BTreeMap::new();

    let numas: Vec<_> = numa_to_mem.keys().copied().collect();
    for numa_id in numas.iter() {
        let page_allocator = init_dma(*numa_id, &mut numa_to_mem, &mut page_table);
        page_allocators.insert(*numa_id, page_allocator);
    }

    for (cpu, numa) in cpu_to_numa.iter() {
        log::info!("CPU/NUMA: {cpu}/{numa}");
    }

    // 9. Initialize stack memory regions for non-primary CPUs.
    if map_stack(&cpu_to_numa, &mut page_table, &mut page_allocators).is_err() {
        log::error!("Failed to map stack memory.");
        wait_forever();
    }

    unsafe { set_raw_cpu_id_to_numa(cpu_to_numa) };

    let (type_apic, mpboot_start) = if let Some(page_allocator0) = page_allocators.get_mut(&0) {
        // 10. Initialize `awkernel_lib` and `awkernel_driver`
        let mut awkernel_page_table = page_table::PageTable::new(&mut page_table);
        if let Err(e) =
            awkernel_lib::arch::x86_64::init(&acpi, &mut awkernel_page_table, page_allocator0)
        {
            log::error!("Failed to initialize `awkernel_lib`. {}", e);
            wait_forever();
        }

        // 11. Initialize APIC.
        let type_apic = awkernel_drivers::interrupt_controller::apic::new(
            &mut awkernel_page_table,
            page_allocator0,
        );

        // 12. Map a page for `mpboot.img`.
        let mpboot_start = map_mpboot_page(boot_info, &mut awkernel_page_table, page_allocator0);

        (type_apic, mpboot_start)
    } else {
        log::error!("No page allocator for NUMA #0.");
        awkernel_lib::delay::wait_forever();
    };

    // 13. Write boot images to wake non-primary CPUs up.
    write_boot_images(offset, mpboot_start);

    // 14. Boot non-primary CPUs.
    log::info!("Waking non-primary CPUs up.");

    let mut non_primary_cpus = BTreeSet::new();

    if let Ok(platform_info) = acpi.platform_info() {
        if let Some(processor_info) = platform_info.processor_info {
            for p in processor_info.application_processors.iter() {
                if matches!(p.state, ProcessorState::WaitingForSipi)
                    && (matches!(type_apic, TypeApic::Xapic(_)) && p.local_apic_id < 255
                        || matches!(type_apic, TypeApic::X2Apic(_)))
                {
                    non_primary_cpus.insert(p.local_apic_id);
                }
            }
        } else {
            log::error!("Failed to get the processor information.");
            wait_forever();
        }
    } else {
        log::error!("Failed to get the platform information.");
        wait_forever();
    };

    let mut cpu_mapping = BTreeMap::<usize, usize>::new();
    for (cpu_id, raw_cpu_id) in non_primary_cpus.iter().enumerate() {
        let cpu_id = cpu_id + 1; // Non-primary CPU ID starts from 1.
        cpu_mapping.insert(*raw_cpu_id as usize, cpu_id);
        log::info!("Raw CPU ID/CPU ID: {raw_cpu_id}/{cpu_id}");
    }
    unsafe { awkernel_lib::arch::x86_64::cpu::set_raw_cpu_id_to_cpu_id(cpu_mapping) };

    let apic_result = match type_apic {
        TypeApic::Xapic(mut xapic) => {
            let result = wake_non_primary_cpus(&xapic, &non_primary_cpus, offset, mpboot_start);

            // Initialize timer.
            init_apic_timer(&mut xapic);

            // Register interrupt controller.
            unsafe { register_interrupt_controller(Box::new(xapic)) };

            result
        }
        TypeApic::X2Apic(mut x2apic) => {
            let result = wake_non_primary_cpus(&x2apic, &non_primary_cpus, offset, mpboot_start);

            // Initialize the interrupt remapping table.
            if let Err(e) = unsafe {
                init_interrupt_remap(
                    awkernel_lib::addr::virt_addr::VirtAddr::new(offset as usize),
                    &acpi,
                    true,
                )
            } {
                log::error!("Failed to initialize interrupt remapping table. {}", e);
                wait_forever();
            }

            // Initialize timer.
            init_apic_timer(&mut x2apic);

            // Register interrupt controller.
            unsafe { register_interrupt_controller(Box::new(x2apic)) };

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

    // 15. Initialize the primary heap memory allocator.
    init_primary_heap(&mut page_table, &mut page_allocators);

    // 16. Initialize PCIe devices.
    if awkernel_drivers::pcie::init_with_acpi(&acpi, 255, 32).is_err() {
        // fallback
        awkernel_drivers::pcie::init_with_io(255, 32);
    }

    // 17. Initialize interrupt handlers.
    unsafe { interrupt_handler::init() };

    if let Some(framebuffer) = boot_info.framebuffer.take() {
        let info = framebuffer.info();
        let buffer = framebuffer.into_buffer();

        log::info!(
            "Framebuffer: width = {}, height = {}, pixel_format = {:?}",
            info.width,
            info.height,
            info.pixel_format
        );

        unsafe { awkernel_drivers::ic::x86_64::lfb::init(info, buffer) };
    }

    BSP_READY.store(true, Ordering::SeqCst);

    while BOOTED_APS.load(Ordering::Relaxed) != 0 {
        core::hint::spin_loop();
    }

    // 18. Synchronize TSC.
    unsafe { synchronize_tsc(non_primary_cpus.len() + 1) };

    log::info!("All CPUs are ready.");

    let kernel_info = KernelInfo {
        info: Some(boot_info),
        cpu_id: 0,
        num_cpu: non_primary_cpus.len() + 1,
    };

    // 19. Call `crate::main()`.
    crate::main(kernel_info);
}

fn init_apic_timer(apic: &mut dyn Apic) {
    apic.write_timer_div(1);

    let mut total = 0;
    for _ in 0..10 {
        apic.write_timer_initial_count(!0);
        awkernel_lib::delay::wait_microsec(20);

        let diff = !0 - apic.read_current_timer_count();
        total += diff;
    }

    let timer = apic.create_timer(1, total / 10);
    awkernel_lib::timer::register_timer(timer);
}

fn init_primary_heap(
    page_table: &mut OffsetPageTable<'static>,
    page_allocators: &mut BTreeMap<u32, VecPageAllocator>,
) {
    let primary_start = HEAP_START + BACKUP_HEAP_SIZE;

    let num_pages = map_primary_heap(page_table, page_allocators, primary_start);

    let heap_size = num_pages * PAGESIZE;
    unsafe { awkernel_lib::heap::init_primary(primary_start, heap_size) };

    log::info!(
        "Primary heap: start = 0x{:x}, size = {}MiB",
        primary_start,
        heap_size / 1024 / 1024
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

// const NON_PRIMARY_START: u64 = 0; // Entry point of 16-bit mode (protected mode).
const NON_PRIMARY_KERNEL_MAIN: u64 = 2048;
const CR3_POS: u64 = NON_PRIMARY_KERNEL_MAIN + 8;
const CPU_ID_POS: u64 = CR3_POS + 8;

fn write_boot_images(offset: u64, mpboot_start: u64) {
    // Calculate address.
    let mpboot = include_bytes!("../../../asm/x86/mpboot.img");
    let mpboot_phy_addr = VirtAddr::new(mpboot_start + offset);

    let main_addr = VirtAddr::new(NON_PRIMARY_KERNEL_MAIN + offset + mpboot_start);
    let cr3_phy_addr = VirtAddr::new(CR3_POS + offset + mpboot_start);
    let cpu_id_addr = VirtAddr::new(CPU_ID_POS + offset + mpboot_start);

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

        // Write CPU ID.
        write_volatile(cpu_id_addr.as_mut_ptr(), 1);

        asm!(
            "wbinvd
             mfence"
        );
    }
}

fn wake_non_primary_cpus(
    apic: &dyn Apic,
    non_primary_cpus: &BTreeSet<u32>,
    offset: u64,
    mpboot_start: u64,
) -> Result<(), &'static str> {
    NUM_CPUS.store(non_primary_cpus.len() + 1, Ordering::SeqCst);
    BOOTED_APS.store(non_primary_cpus.len(), Ordering::Release);

    for (i, ap) in non_primary_cpus.iter().enumerate() {
        send_ipi(apic, *ap, offset, mpboot_start, i as u64 + 1);
    }

    console::print("\r\n");
    log::info!("Sent IPIs to wake non-primary CPUs up.");

    Ok(())
}

fn send_ipi(apic: &dyn Apic, apic_id: u32, offset: u64, mpboot_start: u64, cpu_id: u64) {
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
        (mpboot_start >> 12) as u8,
    );

    wait_microsec(200); // Wait 200[us]

    let cpu_id_addr = VirtAddr::new(CPU_ID_POS + offset + mpboot_start);
    unsafe {
        while read_volatile::<u64>(cpu_id_addr.as_ptr()) == cpu_id {
            core::hint::spin_loop();
        }
    }

    // SIPI
    apic.interrupt(
        apic_id,
        DestinationShorthand::NoShorthand,
        IcrFlags::ASSERT,
        DeliveryMode::StartUp,
        (mpboot_start >> 12) as u8,
    );

    wait_microsec(200); // Wait 200[us]
}

#[inline(never)]
fn non_primary_kernel_main() -> ! {
    while !BSP_READY.load(Ordering::Relaxed) {
        core::hint::spin_loop();
    }
    fence(Ordering::Acquire);

    enable_fpu(); // Enable SSE.

    unsafe { interrupt_handler::load() };

    // use the primary and backup allocator
    unsafe { awkernel_lib::heap::TALLOC.use_primary_then_backup() };

    BOOTED_APS.fetch_sub(1, Ordering::Relaxed);

    while BOOTED_APS.load(Ordering::Relaxed) != 0 {
        core::hint::spin_loop();
    }

    let cpu_id = awkernel_lib::cpu::cpu_id();
    let num_cpu = NUM_CPUS.load(Ordering::Relaxed);

    unsafe { synchronize_tsc(num_cpu) };

    let kernel_info = KernelInfo::<Option<&mut BootInfo>> {
        info: None,
        cpu_id,
        num_cpu,
    };

    crate::main(kernel_info); // jump to userland

    wait_forever();
}

fn map_mpboot_page(
    boot_info: &mut BootInfo,
    page_table: &mut awkernel_lib::arch::x86_64::page_table::PageTable,
    page_allocator: &mut VecPageAllocator,
) -> u64 {
    let start = if let Some(region) = boot_info
        .memory_regions
        .iter()
        .find(|r| r.kind == MemoryRegionKind::Usable && r.start < MPBOOT_REGION_END)
    {
        region.start
    } else {
        unsafe { unsafe_puts("No page is available for `mpboot.img`. Forces use of page #0.\r\n") };
        0
    };

    let flags = awkernel_lib::paging::Flags {
        execute: true,
        write: true,
        cache: false,
        device: false,
        write_through: false,
    };

    unsafe {
        match page_table.map_to(
            awkernel_lib::addr::virt_addr::VirtAddr::new(start as usize),
            awkernel_lib::addr::phy_addr::PhyAddr::new(start as usize),
            flags,
            page_allocator,
        ) {
            Ok(_) => start,
            Err(_) => {
                unsafe_puts("Failed to map the page for `mpboot.img`.\r\n");
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
            && region.start >= MPBOOT_REGION_END
            && region.end - region.start >= BACKUP_HEAP_SIZE as u64 * 2
        {
            backup_heap_region = Some(*region);
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

    let backup_pages = map_backup_heap(
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
        awkernel_lib::heap::TALLOC.use_primary_then_backup();
    }

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

    // Collect the topology information.
    if let Ok(srat) = acpi.find_table::<awkernel_lib::arch::x86_64::acpi::srat::Srat>() {
        for entry in srat.entries() {
            match entry {
                awkernel_lib::arch::x86_64::acpi::srat::SratEntry::MemoryAffinity(affinity) => {
                    if affinity.flags & 1 == 0 {
                        continue;
                    }

                    let start = affinity.lo_base as usize | ((affinity.hi_base as usize) << 32);
                    let length =
                        affinity.lo_length as usize | ((affinity.hi_length as usize) << 32);

                    numa_id_to_memory
                        .entry(affinity.domain)
                        .or_insert_with(Vec::new)
                        .push((start, length));
                }
                awkernel_lib::arch::x86_64::acpi::srat::SratEntry::LocalApic(srat_apic) => {
                    if srat_apic.flags & 1 == 0 {
                        continue;
                    }

                    let domain = srat_apic.lo_dm as u32
                        | ((srat_apic.hi_dm[0] as u32) << 8)
                        | ((srat_apic.hi_dm[1] as u32) << 16)
                        | ((srat_apic.hi_dm[2] as u32) << 24);
                    cpu_to_numa_id.insert(srat_apic.apic_id as u32, domain);
                }
                awkernel_lib::arch::x86_64::acpi::srat::SratEntry::LocalX2Apic(srat_apic) => {
                    if srat_apic.flags & 1 == 0 {
                        continue;
                    }

                    let domain = srat_apic.domain;
                    cpu_to_numa_id.insert(srat_apic.x2apic_id, domain);
                }
                _ => (),
            }
        }
    } else if let Ok(info) = acpi.platform_info() {
        if let Some(processor) = &info.processor_info {
            cpu_to_numa_id.insert(processor.boot_processor.local_apic_id, 0);

            for p in processor.application_processors.iter() {
                cpu_to_numa_id.insert(p.local_apic_id, 0);
            }

            for mem in boot_info
                .memory_regions
                .iter()
                .filter(|m| m.kind == MemoryRegionKind::Usable && m.start >= MPBOOT_REGION_END)
            {
                numa_id_to_memory
                    .entry(0)
                    .or_insert_with(Vec::new)
                    .push((mem.start as usize, mem.end as usize - mem.start as usize));
            }
        } else {
            log::error!("Failed to get processor information.");
            awkernel_lib::delay::wait_forever();
        }
    } else {
        log::error!("Failed to get topology information.");
        awkernel_lib::delay::wait_forever();
    }

    let mut memory_regions = BTreeMap::new();

    let mut usable_regions: VecDeque<MemoryRegion> = boot_info
        .memory_regions
        .iter()
        .filter(|m| m.kind == MemoryRegionKind::Usable && m.start >= MPBOOT_REGION_END)
        .copied()
        .collect();

    loop {
        let Some(usable_region) = usable_regions.pop_front() else {
            break;
        };

        let usable_region = if usable_region.start == backup_region.start {
            if let Some(frame) = backup_next_frame {
                // Exclude the backup heap memory region.
                MemoryRegion {
                    start: frame.start_address().as_u64(),
                    end: usable_region.end,
                    kind: MemoryRegionKind::Usable,
                }
            } else {
                continue;
            }
        } else {
            usable_region
        };

        if usable_region.start == 0 || usable_region.start == usable_region.end {
            continue;
        }

        fn wrap_up(addr: u64) -> u64 {
            (addr.checked_add(PAGESIZE as u64 - 1).unwrap()) & !(PAGESIZE as u64 - 1)
        }

        fn wrap_down(addr: u64) -> u64 {
            addr & !(PAGESIZE as u64 - 1)
        }

        let usable_start = wrap_up(usable_region.start);
        let usable_end = wrap_down(usable_region.end);

        'outer: for (numa_id, mems) in numa_id_to_memory.iter() {
            for (start, length) in mems.iter() {
                let end = *start + *length;
                if (*start..end).contains(&(usable_start as usize)) {
                    if (*start..=end).contains(&(usable_end as usize)) {
                        memory_regions
                            .entry(*numa_id)
                            .or_insert_with(Vec::new)
                            .push(usable_region);

                        break 'outer;
                    } else {
                        let remain = MemoryRegion {
                            start: end as u64,
                            end: usable_end,
                            kind: MemoryRegionKind::Usable,
                        };

                        memory_regions
                            .entry(*numa_id)
                            .or_insert_with(Vec::new)
                            .push(usable_region);

                        usable_regions.push_front(remain);

                        break 'outer;
                    }
                }
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
    let mut dma_phy_region = None;

    let Some(mut numa_memory) = numa_memory.remove(&numa_id) else {
        log::error!("Failed to get NUMA memory. NUMA ID = {}", numa_id);
        awkernel_lib::delay::wait_forever();
    };

    for region in numa_memory.iter_mut() {
        let end = region.start + DMA_SIZE as u64;
        if region.end - region.start >= DMA_SIZE as u64 {
            dma_phy_region = Some(MemoryRegion {
                start: region.start,
                end,
                kind: MemoryRegionKind::Usable,
            });

            region.start = end;

            break;
        }
    }

    let Some(dma_phy_region) = dma_phy_region else {
        log::error!("Failed to allocate a DMA region. NUMA ID = {}", numa_id);
        awkernel_lib::delay::wait_forever();
    };

    let mut page_allocator = page_allocator::VecPageAllocator::new(numa_memory);
    let dma_start = DMA_START + numa_id as usize * DMA_SIZE;
    let flags = PageTableFlags::PRESENT
        | PageTableFlags::WRITABLE
        // | PageTableFlags::NO_CACHE
        | PageTableFlags::NO_EXECUTE
        | PageTableFlags::GLOBAL;

    for (i, dma_phy_frame) in (dma_phy_region.start..dma_phy_region.end)
        .step_by(PAGESIZE as _)
        .map(|addr| PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(addr)))
        .enumerate()
    {
        let virt_frame = Page::containing_address(VirtAddr::new((dma_start + i * PAGESIZE) as u64));

        unsafe {
            page_table
                .map_to(virt_frame, dma_phy_frame, flags, &mut page_allocator)
                .unwrap()
                .flush()
        };
    }

    log::info!(
        "DMA(NUMA #{}): start = 0x{:x}, size = {}MiB",
        numa_id,
        dma_start,
        DMA_SIZE / 1024 / 1024
    );

    unsafe {
        awkernel_lib::dma_pool::init_dma_pool(
            numa_id as usize,
            awkernel_lib::addr::virt_addr::VirtAddr::new(dma_start),
            (dma_phy_region.end - dma_phy_region.start) as usize,
        )
    };

    page_allocator
}
