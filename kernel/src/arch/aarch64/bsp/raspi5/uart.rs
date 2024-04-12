use awkernel_drivers::raspi5::raspi5_uart;

const ARM_IO_BASE: usize = 0x0010_7C00_0000;
const ARM_UART0_BASE: usize = ARM_IO_BASE + 0x0100_1000;

pub fn init_uart() {
    let uart0 = raspi5_uart::Uart::new(ARM_UART0_BASE);
    uart0.init();
    uart0.send_string("hello world");
}
