use super::driver::uart::{DevUART, UART};
use crate::board_info::BoardInfo;

/// entry point from assembly code
#[no_mangle]
pub extern "C" fn kernel_main() -> ! {
    super::mmu::init_memory_map();

    if super::mmu::init().is_none() {
        let serial = DevUART::new(super::bsp::memory::UART0_BASE);
        serial.init(super::serial::UART_CLOCK, super::serial::UART_BAUD);
        serial.write_str("Failed to init MMU.\n");
        loop {}
    }

    super::serial::init();

    let board_info = BoardInfo::<()> { info: () };

    crate::main::<()>(&board_info);

    loop {}
}
