use bootloader::{entry_point, BootInfo};

use crate::board_info::BoardInfo;

entry_point!(kernel_main);

fn kernel_main(boot_info: &'static mut BootInfo) -> ! {
    let board_info = BoardInfo { info: boot_info };

    if let Some(framebuffer) = board_info.info.framebuffer.as_mut() {
        for byte in framebuffer.buffer_mut() {
            *byte = 0x90;
        }
    }

    crate::main::<_, super::heap::HeapMapper>(&board_info);

    loop {}
}
