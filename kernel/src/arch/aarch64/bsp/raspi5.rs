use super::{DeviceTreeNodeRef, DeviceTreeRef, StaticArrayedNode};
use crate::arch::aarch64::{
    interrupt_ctl,
    vm::{self, VM},
};
use alloc::{boxed::Box, format};

use awkernel_drivers::raspi5::*;

use core::ptr::{read_volatile, write_volatile};

mod pciebridge;
use awkernel_lib::{
    addr::phy_addr::PhyAddr,
    arch::aarch64::{armv8_timer::Armv8Timer, set_max_affinity},
    console::{register_console, register_unsafe_puts, unsafe_puts},
    device_tree::{
        prop::{PropertyValue, Range},
        traits::HasNamedChildNode,
    },
    err_msg,
    paging::PAGESIZE,
};
use core::arch::asm;

pub mod config;
// mod gpio;
mod uart;

fn start_non_primary() {
    unsafe {
        asm!("
mov {0}, #0xe0
ldr {1}, =_start
str {1}, [{0}]     // core #1
str {1}, [{0},  8] // core #2
str {1}, [{0}, 16] // core #3
sev",
            lateout(reg) _,
            lateout(reg) _
        );
    }
}

#[repr(C)]
struct GpioRegs {
    status: u32,
    ctrl: u32,
}

#[repr(C)]
struct RioRegs {
    out: u32,
    oe: u32,
    input: u32,
    in_sync: u32,
}

pub struct Raspi5 {
    symbols: Option<DeviceTreeNodeRef>,
    interrupt: Option<StaticArrayedNode>,
    interrupt_compatible: &'static str,
    local_interrupt: Option<StaticArrayedNode>,
    local_interrupt_compatible: Option<&'static str>,
    device_tree: Option<DeviceTreeRef>,
    device_tree_base: usize,
    uart_base: Option<usize>,
    uart_irq: Option<u16>,
}

impl super::SoC for Raspi5 {
    unsafe fn init_device(&mut self) -> Result<(), &'static str> {
        self.init_pcie_bridge();
        self.init_uart();
        self.init_gpio();
        Ok(())
    }

    unsafe fn init_virtual_memory(&mut self) -> Result<VM, &'static str> {
        let mut vm = VM::new();

        Ok(vm)
    }

    unsafe fn init(&self) -> Result<(), &'static str> {
        Ok(())
    }
}

impl Raspi5 {
    pub const fn new(device_tree_base: usize) -> Self {
        Raspi5 {
            symbols: None,
            interrupt: None,
            interrupt_compatible: "",
            local_interrupt: None,
            local_interrupt_compatible: None,
            device_tree: None,
            device_tree_base,
            uart_base: None,
            uart_irq: None,
        }
    }

    pub fn init_uart(&mut self) {
        uart::init_uart();
    }

    pub fn init_gpio(&mut self) {
        let gpio_pin_14 = raspi5_gpio::GPIOPin::new(14);
        gpio_pin_14.set_alternate_function(4);
        let gpio_pin_2 = raspi5_gpio::GPIOPin::new(2);
        gpio_pin_2.set_mode(raspi5_gpio::GPIOMode::Output);
        for n in 1..10 {
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
