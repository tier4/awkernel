use bootloader::{entry_point, BootInfo};

use crate::{arch::Delay, board_info::BoardInfo};

use super::interrupt;

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

    unsafe { interrupt::init() };

    let board_info = BoardInfo { info: kernel_info };
    crate::main(&board_info);

    super::delay::ArchDelay::wait_forever();
}
