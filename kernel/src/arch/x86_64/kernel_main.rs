use bootloader::{entry_point, BootInfo};

use crate::{arch::Delay, board_info::BoardInfo};

extern "C" {
    static __boot: u64;
}

entry_point!(kernel_main);

fn kernel_main(boot_info: &'static mut BootInfo) -> ! {
    super::serial::init(); // Initialize a serial port and logger.

    if super::heap::HeapMapper::init(boot_info).is_err() {
        super::serial::puts("Failed to map heap memory");
        loop {}
    }

    let board_info = BoardInfo { info: boot_info };

    crate::main(&board_info);

    super::delay::ArchDelay::wait_forever();
}
