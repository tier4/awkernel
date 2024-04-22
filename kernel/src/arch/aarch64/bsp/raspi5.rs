use crate::arch::aarch64::bsp::raspi5::uart::unsafe_puts;
use crate::arch::aarch64::vm::VM;
use awkernel_lib::console::register_unsafe_puts;

use awkernel_drivers::raspi5::*;

pub mod config;
mod pciebridge;
mod uart;

pub struct Raspi5 {}

impl super::SoC for Raspi5 {
    unsafe fn init_device(&mut self) -> Result<(), &'static str> {
        self.init_pcie_bridge();
        self.init_uart();
        self.init_gpio();
        Ok(())
    }

    unsafe fn init_virtual_memory(&mut self) -> Result<VM, &'static str> {
        let vm = VM::new();
        // const MEM_IOMEM_START: u64 = 0x1060000000;
        // const MEM_IOMEM_END: u64 = 0x107FFFFFFF;
        // vm.push_device_range(
        //     PhyAddr::new(MEM_IOMEM_START as usize),
        //     PhyAddr::new(MEM_IOMEM_END as usize),
        // )
        // .expect("Failed to add I/O memory range");
        // vm.set_num_cpus(4);
        // vm.print();
        Ok(vm)
    }

    unsafe fn init(&self) -> Result<(), &'static str> {
        Ok(())
    }
}

impl Raspi5 {
    pub const fn new(_device_tree_base: usize) -> Self {
        Raspi5 {}
    }

    pub fn init_uart(&mut self) {
        uart::init();

        register_unsafe_puts(uart::unsafe_puts);

        unsafe { unsafe_puts("uart0 has been successfully initialized.\r\n") };
    }

    pub fn init_gpio(&mut self) {
        let gpio_pin_14 = raspi5_gpio::GPIOPin::new(14);
        gpio_pin_14.set_alternate_function(4);
        let gpio_pin_2 = raspi5_gpio::GPIOPin::new(2);
        gpio_pin_2.set_mode(raspi5_gpio::GPIOMode::Output);
        for _n in 1..10 {
            gpio_pin_2.write(true);
            awkernel_lib::delay::wait_microsec(1000000);
            gpio_pin_2.write(false);
            awkernel_lib::delay::wait_microsec(1000000);
        }
    }

    pub fn init_pcie_bridge(&mut self) {
        pciebridge::init_pcie_bridge();
    }
}
