use bootloader::{entry_point, BootInfo};

use crate::{board_info::BoardInfo, heap::HeapInit};

entry_point!(kernel_main);

fn kernel_main(boot_info: &'static mut BootInfo) -> ! {
    super::serial::init(); // Initialize a serial port and logger.

    let board_info = BoardInfo { info: boot_info };

    if let Some(framebuffer) = board_info.info.framebuffer.as_mut() {
        for byte in framebuffer.buffer_mut() {
            *byte = 0x90;
        }
    }

    if super::heap::HeapMapper::init(&board_info).is_err() {
        log::error!("Failed to map heap memory. ({}:{})", file!(), line!());
        loop {}
    }

    crate::main(&board_info);

    loop {}
}
