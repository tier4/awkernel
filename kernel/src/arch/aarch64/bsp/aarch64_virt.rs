use awkernel_lib::{
    device_tree::{prop::PropertyValue, traits::HasNamedChildNode},
    err_msg,
};

use crate::arch::aarch64::{bsp::aarch64_virt::uart::unsafe_puts, interrupt_ctl};

use super::{DeviceTreeNodeRef, DeviceTreeRef};

pub mod config;
mod uart;

pub struct AArch64Virt {
    device_tree: DeviceTreeRef,
    device_tree_base: usize,
    interrupt: Option<DeviceTreeNodeRef>,
    interrupt_compatible: &'static str,
}

impl super::SoC for AArch64Virt {
    unsafe fn init_device(&mut self) -> Result<(), &'static str> {
        self.init_interrupt_fields()?;
        self.init_uart()?;
        awkernel_lib::device_tree::print_device_tree_node(self.device_tree.root(), 0);

        unsafe_puts(self.interrupt_compatible);
        unsafe_puts("\n");

        loop {}
        todo!()
    }

    unsafe fn init_virtual_memory(&self) -> Result<crate::arch::aarch64::vm::VM, &'static str> {
        todo!()
    }

    unsafe fn init(&self) -> Result<(), &'static str> {
        todo!()
    }
}

impl AArch64Virt {
    pub fn new(device_tree: DeviceTreeRef, device_tree_base: usize) -> Self {
        AArch64Virt {
            device_tree,
            device_tree_base,
            interrupt: None,
            interrupt_compatible: "",
        }
    }

    unsafe fn init_uart(&self) -> Result<(), &'static str> {
        let chosen_node = self
            .device_tree
            .root()
            .find_child("chosen")
            .ok_or(err_msg!("failed to get chosen"))?;

        let stdout_path = chosen_node
            .get_property("stdout-path")
            .ok_or(err_msg!("failed to get stdout-path"))?;

        let abs_path = match stdout_path.value() {
            PropertyValue::String(p) => *p,
            _ => return Err(err_msg!("__symbols__ is not a string")),
        };

        let uart_node = self
            .device_tree
            .root()
            .get_arrayed_node(abs_path)
            .or(Err(err_msg!("invalid path")))?;

        let leaf = uart_node.get_leaf_node().unwrap();

        // Get "compatible" property.
        let compat_prop = leaf
            .get_property("compatible")
            .ok_or(err_msg!("failed to get compatible property"))?;

        match compat_prop.value() {
            PropertyValue::Strings(ss) => {
                if !ss.contains(&"arm,pl011") {
                    return Err(err_msg!("stdout-path is not arm,pl011"));
                }
            }
            PropertyValue::String(s) => {
                if *s != "arm,pl011" {
                    return Err(err_msg!("stdout-path is not arm,pl011"));
                }
            }
            _ => {
                return Err(err_msg!("invalid compatible property"));
            }
        }

        // Get the base address.
        let base = uart_node
            .get_address(0)
            .or(Err(err_msg!("failed to get the base address")))?;

        // Get interrupts.
        let interrupts_prop = leaf
            .get_property("interrupts")
            .ok_or(err_msg!("failed to get interrupts"))?;

        let interrupts = match interrupts_prop.value() {
            PropertyValue::Integers(v) => v,
            _ => return Err(err_msg!("interrupts property has invalid value")),
        };

        let irq = interrupt_ctl::get_irq(self.interrupt_compatible, interrupts)
            .ok_or(err_msg!("failed to calculate IRQ#"))?;

        // Get clock.
        let clock_prop = leaf
            .get_property("clocks")
            .ok_or(err_msg!("failed to get clocks property"))?;

        let clock = match clock_prop.value() {
            PropertyValue::Integers(clocks) => {
                clocks.get(0).ok_or(err_msg!("clocks has invalid value"))?
            }
            _ => return Err(err_msg!("clocks property has invalid value")),
        };

        // Initialize UART.
        uart::init(base as usize, irq, *clock as usize);

        Ok(())
    }

    fn init_interrupt_fields(&mut self) -> Result<(), &'static str> {
        let intc = self
            .device_tree
            .root()
            .nodes()
            .iter()
            .find(|n| n.name().starts_with("intc@"))
            .ok_or(err_msg!("could not find interrupt controller"))?;

        let compatible_prop = intc
            .get_property("compatible")
            .ok_or(err_msg!("interrupt node has no compatible property"))?;

        self.interrupt_compatible = match compatible_prop.value() {
            PropertyValue::String(s) => s,
            _ => return Err(err_msg!("compatible property has not string value")),
        };

        self.interrupt = Some(intc);

        Ok(())
    }

    fn init_interrupt_controller(&self) -> Result<(), &'static str> {
        let Some(intc) = &self.interrupt else {
            return Err(err_msg!("interrupt is not initialized"));
        };

        let reg_prop = intc
            .get_property("reg")
            .ok_or(err_msg!("no reg property"))?;

        let (gicd_base, gicc_base) = match reg_prop.value() {
            PropertyValue::Addresses(addrs) => (
                addrs.get(0).ok_or(err_msg!("no GICD_BASE"))?,
                addrs.get(0).ok_or(err_msg!("no GICC_BASE"))?,
            ),
            _ => {
                return Err(err_msg!("reg property has invalid value"));
            }
        };

        Ok(())
    }
}
