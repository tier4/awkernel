use super::interrupt;
use crate::{arch::Delay, heap, kernel_info::KernelInfo};
use bootloader_api::{config::Mapping, entry_point, BootInfo, BootloaderConfig};
use x86_64::registers::control::{Cr0, Cr0Flags, Cr4, Cr4Flags};

extern "C" {
    static __boot: u64;
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

    if super::heap::HeapMapper::init(boot_info).is_err() {
        super::serial::puts("Failed to map heap memory");
        loop {}
    }

    heap::init(); // Enable heap allocator.
    enable_fpu(); // Enable SSE.
    unsafe { interrupt::init() }; // Initialize interrupt handlers.

    if let Some(offset) = boot_info.physical_memory_offset.as_ref() {
        log::info!("Physical memory offset = {:x}", offset);

        // Initialize APIC.
        super::apic::new(*offset);
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
