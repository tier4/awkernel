//! This module defines the x86_64's entry point.
//!
//! `kernel_main()` function is the entry point and called by `bootloader` crate.

use super::{heap::map_heap, interrupt};
use crate::{
    arch::x86_64::stack::map_stack,
    config::{BACKUP_HEAP_SIZE, HEAP_START, STACK_SIZE},
    kernel_info::KernelInfo,
};
use alloc::boxed::Box;
use awkernel_drivers::interrupt_controller::apic::{
    registers::{DeliveryMode, DestinationShorthand, IcrFlags},
    Apic, TypeApic,
};
use awkernel_lib::{
    arch::x86_64::page_allocator::{self, get_page_table, PageAllocator},
    console::unsafe_puts,
    delay::{wait_forever, wait_microsec},
    interrupt::register_interrupt_controller,
    memory::PAGESIZE,
};
use bootloader_api::{
    config::Mapping, entry_point, info::MemoryRegionKind, BootInfo, BootloaderConfig,
};
use core::{arch::asm, ptr::write_volatile};
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
    config.kernel_stack_size = STACK_SIZE as u64;
    config
};

// Set `kernel_main` as the entry point.
entry_point!(kernel_main, config = &BOOTLOADER_CONFIG);

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
/// 10. Initialize the primary heap memory allocator.
/// 11. Write boot images to wake non-primary CPUs up.
/// 12. Boot non-primary CPUs.
/// 13. Call `crate::main()`.
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

    // Share the page table.
    // for l4 in page_table.level_4_table().iter_mut() {
    //     let flags = l4.flags();
    //     l4.set_flags(flags | PageTableFlags::GLOBAL);
    // }

    // let cr4 = x86_64::registers::control::Cr4::read();
    // unsafe {
    //     x86_64::registers::control::Cr4::write(
    //         cr4 | x86_64::registers::control::Cr4Flags::PAGE_GLOBAL,
    //     )
    // };

    // Create a page allocator.
    let mut frames = boot_info
        .memory_regions
        .iter()
        .filter(|m| m.kind == MemoryRegionKind::Usable && m.start != 0)
        .flat_map(|m| (m.start..m.end).step_by(PAGESIZE as _))
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
                unsafe_puts("Failed to map 0.\r\n");
                wait_forever();
            }
        }
    }

    // Get offset address to physical memory.
    let Some(offset) = boot_info.physical_memory_offset.as_ref() else {
        unsafe { unsafe_puts("Failed to get the physical memory offset.\r\n") };
        wait_forever();
    };
    let offset = *offset;

    let backup_start = HEAP_START;
    let backup_size = BACKUP_HEAP_SIZE;

    // 4. Initialize the backup heap memory allocator.
    // Map backup heap memory region.
    map_heap(
        &mut page_table,
        &mut page_allocator,
        backup_start,
        backup_size,
    );

    // Initialize.
    unsafe { awkernel_lib::heap::init_backup(backup_start, backup_size) }; // Enable heap allocator.

    // Set to use the backup allocator in kernel.
    unsafe { awkernel_lib::heap::TALLOC.use_primary_then_backup() };

    // 5. Enable logger.
    super::console::register_console();

    log::info!(
        "Backup heap: start = 0x{:x}, size = {}",
        backup_start,
        backup_size
    );

    log::info!("Physical memory offset: 0x{:x}", offset);

    // 6. Initialize ACPI.
    let acpi = if let Some(acpi) = awkernel_lib::arch::x86_64::acpi::create_acpi(boot_info, offset)
    {
        acpi
    } else {
        log::error!("Failed to initialize ACPI.");
        wait_forever();
    };

    // 7. Initialize stack memory regions for non-primary CPUs.
    if map_stack(&acpi, &mut page_table, &mut page_allocator).is_err() {
        log::error!("Failed to map stack memory.");
        wait_forever();
    }

    // 8. Initialize `awkernel_lib` and `awkernel_driver`
    awkernel_lib::arch::x86_64::init(&acpi, &mut page_table, &mut page_allocator);
    awkernel_drivers::pcie::init(&acpi, &mut page_table, &mut page_allocator, PAGESIZE as u64);

    // 9. Initialize APIC.
    let type_apic =
        awkernel_drivers::interrupt_controller::apic::new(&mut page_table, &mut page_allocator);

    // 10. Initialize the primary heap memory allocator.
    init_primary_heap(&mut page_table, &mut page_allocator);

    // 11. Write boot images to wake non-primary CPUs up.
    write_boot_images(offset);

    // 12. Boot non-primary CPUs.
    log::info!("Waking non-primary CPUs up.");

    match type_apic {
        TypeApic::Xapic(xapic) => {
            // 12. Boot non-primary CPUs.
            start_non_primary_cpus(&xapic);

            // Register interrupt controller.
            register_interrupt_controller(Box::new(xapic));
        }
        TypeApic::X2Apic(x2apic) => {
            // 12. Boot non-primary CPUs.
            start_non_primary_cpus(&x2apic);

            // Register interrupt controller.
            // register_interrupt_controller(Box::new(x2apic));
        }
        _ => {
            log::error!("Failed to initialize APIC.");
            wait_forever();
        }
    };

    let kernel_info = KernelInfo {
        info: Some(boot_info),
        cpu_id: 0,
    };

    // 13. Call `crate::main()`.
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

const NON_PRIMARY_START: u64 = 0; // 8KiB. Entry point of 16-bit mode (protected mode).
const ENTRY32: u64 = NON_PRIMARY_START + 1024; // 5KiB. Entry point of 32-bit mode (long mode).

const NON_PRIMARY_KERNEL_MAIN: u64 = ENTRY32 + 1024;
const CR3_POS: u64 = NON_PRIMARY_KERNEL_MAIN + 8;
const GDTR_POS: u64 = CR3_POS + 14;

fn write_boot_images(offset: u64) {
    // Calculate address.
    let boot16 = include_bytes!("../../../asm/x86/boot16.img");
    let boot16_phy_addr = VirtAddr::new(NON_PRIMARY_START + offset);

    let entry32 = include_bytes!("../../../asm/x86/entry32.img");
    let entry32_phy_addr = VirtAddr::new(ENTRY32 + offset);

    let main_addr = VirtAddr::new(NON_PRIMARY_KERNEL_MAIN + offset);
    let cr3_phy_addr = VirtAddr::new(CR3_POS + offset);
    let gdtr_addr = VirtAddr::new(GDTR_POS + offset);

    // Store CR3.
    let mut cr3: u64;
    unsafe { asm!("mov {}, cr3", out(reg) cr3, options(nomem, nostack, preserves_flags)) };

    let mut gdtr: [u8; 10] = [0; 10];

    unsafe {
        asm!(
            "sgdt [{}]",
            in(reg) &gdtr,
            options(nostack)
        );
    }

    let mut cs = 0;
    unsafe { asm!("mov {0:e}, cs", out(reg) cs, options(nomem, nostack, preserves_flags)) };

    log::debug!("CS = 0x{cs:02x}");

    unsafe {
        // Write boot16.img.
        log::info!("write boot16.img to 0x{boot16_phy_addr:08x}");
        write_volatile(boot16_phy_addr.as_mut_ptr(), *boot16);

        // Write entry32.img.
        log::info!("write entry32.img to 0x{entry32_phy_addr:08x}");
        write_volatile(entry32_phy_addr.as_mut_ptr(), *entry32);

        // Write non_primary_kernel_main.
        log::info!(
            "write the kernel entry of 0x{:08x} to 0x{main_addr:08x}",
            non_primary_kernel_main as usize
        );
        write_volatile(main_addr.as_mut_ptr(), non_primary_kernel_main as usize);

        // Write CR3.
        log::info!("write CR3 of 0x{cr3:08x} to 0x{cr3_phy_addr:08x}");
        write_volatile(cr3_phy_addr.as_mut_ptr(), cr3);

        log::info!("write GDTR to 0x{cr3_phy_addr:08x}");
        write_volatile(gdtr_addr.as_mut_ptr(), gdtr);

        asm!(
            "mfence
             wbinvd"
        );
    }
}

fn start_non_primary_cpus(apic: &dyn Apic) {
    // INIT IPI, ASSERT
    apic.interrupt(
        1,
        DestinationShorthand::NoShorthand,
        IcrFlags::ASSERT | IcrFlags::LEVEL_TRIGGER,
        DeliveryMode::Init,
        0,
    );

    wait_microsec(10_000); // Wait 10[ms]
    unsafe { unsafe_puts("V") };

    // INIT IPI, DEASSERT
    apic.interrupt(
        1,
        DestinationShorthand::NoShorthand,
        IcrFlags::LEVEL_TRIGGER,
        DeliveryMode::Init,
        0,
    );

    wait_microsec(10_000); // Wait 10[ms]

    // SIPI
    apic.interrupt(
        1,
        DestinationShorthand::NoShorthand,
        IcrFlags::ASSERT,
        DeliveryMode::StartUp,
        (NON_PRIMARY_START >> 12) as u8,
    );

    unsafe { unsafe_puts("W") };
    wait_microsec(200); // Wait 200[us]
    unsafe { unsafe_puts("X") };

    loop {
        awkernel_lib::delay::wait_sec(1);
        unsafe {
            unsafe_puts("Z");
        }
    }

    // SIPI
    apic.interrupt(
        1,
        DestinationShorthand::NoShorthand,
        IcrFlags::ASSERT,
        DeliveryMode::StartUp,
        (NON_PRIMARY_START >> 12) as u8,
    );
    unsafe { unsafe_puts("Y") };

    wait_microsec(200); // Wait 200[us]

    loop {
        awkernel_lib::delay::wait_sec(1);
        unsafe {
            unsafe_puts("Z");
        }
    }
}

#[inline(never)]
fn non_primary_kernel_main() -> ! {
    let ebx = unsafe { core::arch::x86_64::__cpuid(1).ebx };
    let cpu_id = (ebx >> 24) & 0xff;

    enable_fpu(); // Enable SSE.

    // unsafe { unsafe_puts("F") };

    let mut port = unsafe { awkernel_drivers::uart::uart_16550::SerialPort::new(0x3F8) };

    port.send(b'F');

    loop {}

    // use the primary and backup allocator
    unsafe { awkernel_lib::heap::TALLOC.use_primary_then_backup() };

    // Initialize interrupt handlers.
    unsafe { interrupt::init() };

    let kernel_info = KernelInfo::<Option<&mut BootInfo>> {
        info: None,
        cpu_id: cpu_id as usize,
    };

    crate::main(kernel_info); // jump to userland

    wait_forever();
}
