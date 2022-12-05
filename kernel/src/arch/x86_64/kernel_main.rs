use super::interrupt;
use crate::{arch::Delay, board_info::BoardInfo};
use bootloader::{entry_point, BootInfo};
use x86_64::registers::control::{Cr0, Cr0Flags, Cr4, Cr4Flags};

extern "C" {
    static __boot: u64;
    static __eh_frame: u64;
}

#[derive(Debug)]
pub struct KernelInfo {
    boot_info: &'static mut BootInfo,
    eh_frame: u64,
}

entry_point!(kernel_main);

fn kernel_main(boot_info: &'static mut BootInfo) -> ! {
    super::serial::init(); // Initialize a serial port and logger.

    if super::heap::HeapMapper::init(boot_info).is_err() {
        super::serial::puts("Failed to map heap memory");
        loop {}
    }

    let kernel_info = KernelInfo {
        boot_info,
        eh_frame: unsafe { &__eh_frame as *const u64 as u64 },
    };

    enable_fpu(); // Enable SSE.

    unsafe { interrupt::init() }; // Initialize interrupt handlers.

    let board_info = BoardInfo { info: kernel_info };
    crate::main(&board_info);

    super::delay::ArchDelay::wait_forever();
}

pub fn enable_fpu() {
    let mut cr0flags = Cr0::read();
    cr0flags &= !Cr0Flags::EMULATE_COPROCESSOR;
    cr0flags |= Cr0Flags::MONITOR_COPROCESSOR;

    unsafe { Cr0::write(cr0flags) };

    let mut cr4flags = Cr4::read();
    cr4flags |= Cr4Flags::OSFXSR | Cr4Flags::OSXMMEXCPT_ENABLE;

    unsafe { Cr4::write(cr4flags) };
}
