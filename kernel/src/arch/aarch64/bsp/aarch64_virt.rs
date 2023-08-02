use alloc::boxed::Box;
use awkernel_drivers::{
    psci::{self, Affinity},
    uart::pl011::PL011,
};
use awkernel_lib::{
    arch::aarch64::{armv8_timer::Armv8Timer, set_max_affinity},
    console::register_console,
    device_tree::{prop::PropertyValue, traits::HasNamedChildNode},
    err_msg,
    memory::PAGESIZE,
};

use crate::arch::aarch64::{
    bsp::aarch64_virt::uart::unsafe_puts,
    interrupt_ctl,
    vm::{get_kernel_start, VM},
};

use super::{DeviceTreeRef, StaticArrayedNode};

pub mod config;
mod uart;

const DEVICE_MEM_START: usize = 0x0800_0000;
const DEVICE_MEM_END: usize = 0x4000_0000;
const FLASH_START: usize = 0;
const FLASH_END: usize = 0x0800_0000;

/// IRQ #27 is the recommended value.
/// every 1/2^14 = 0..000_061 [s].
pub static TIMER_ARM_V8: Armv8Timer = Armv8Timer::new(27, 14);

pub struct AArch64Virt {
    device_tree: DeviceTreeRef,
    device_tree_base: usize,
    uart_base: Option<usize>,
    uart_irq: Option<u16>,
    interrupt: Option<StaticArrayedNode>,
    interrupt_compatible: &'static str,
}

impl super::SoC for AArch64Virt {
    unsafe fn init_device(&mut self) -> Result<(), &'static str> {
        self.init_interrupt_fields()?;
        self.init_uart()?;
        awkernel_lib::device_tree::print_device_tree_node(self.device_tree.root(), 0);

        if let Err(err) = self.wake_cpus_up() {
            unsafe_puts(err);
            unsafe_puts("\n");
            return Err(err);
        }

        Ok(())
    }

    unsafe fn init_virtual_memory(&self) -> Result<crate::arch::aarch64::vm::VM, &'static str> {
        let mut vm = VM::new();

        vm.push_device_range(DEVICE_MEM_START, DEVICE_MEM_END)?;
        vm.push_ro_memory(FLASH_START, FLASH_END)?;

        let num_cpus = self
            .device_tree
            .num_cpus()
            .or(Err(err_msg!("failed to count up the number of CPUs")))?;

        vm.set_num_cpus(num_cpus);

        // Add heap memory regions.
        vm.add_heap_from_node(self.device_tree.root())?;

        // Do not use the memory containing kernel's binary for heap memory.
        vm.remove_kernel_memory_from_heap_memory()?;

        let mask = PAGESIZE - 1;
        let start = self.device_tree_base & !mask;
        let end = self.device_tree_base + self.device_tree.total_size();
        let end = end + PAGESIZE - (end & mask);

        vm.remove_heap(start, end)?; // Do not use DTB's memory region for heap memory.
        vm.push_ro_memory(start, end)?; // Make DTB's memory region read-only memory.

        vm.print();
        unsafe_puts("Initializing the page table. Wait a moment.\n");

        vm.init()?;

        Ok(vm)
    }

    unsafe fn init(&self) -> Result<(), &'static str> {
        let uart_base = self
            .uart_base
            .ok_or(err_msg!("UART's base address has not been initialized."))?;

        let uart_irq = self.uart_irq.ok_or(err_msg!("UART's #IRQ is unknown."))?;

        let port = Box::new(PL011::new(uart_base, uart_irq));
        register_console(port);

        self.init_interrupt_controller()?;
        awkernel_lib::timer::register_timer(&TIMER_ARM_V8);

        Ok(())
    }
}

impl AArch64Virt {
    pub fn new(device_tree: DeviceTreeRef, device_tree_base: usize) -> Self {
        AArch64Virt {
            device_tree,
            device_tree_base,
            uart_base: None,
            uart_irq: None,
            interrupt: None,
            interrupt_compatible: "",
        }
    }

    unsafe fn init_uart(&mut self) -> Result<(), &'static str> {
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

        self.uart_base = Some(base as usize);

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

        self.uart_irq = Some(irq);

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

        let mut arrayed_node = StaticArrayedNode::new();
        arrayed_node
            .push(self.device_tree.root())
            .or(Err(err_msg!("failed to push root")))?;
        arrayed_node
            .push(intc)
            .or(Err(err_msg!("failed to push intc")))?;

        self.interrupt = Some(arrayed_node);

        Ok(())
    }

    fn init_interrupt_controller(&self) -> Result<(), &'static str> {
        let Some(intc) = &self.interrupt else {
            return Err(err_msg!("interrupt is not initialized"));
        };

        interrupt_ctl::init_interrupt_controller(self.interrupt_compatible, intc)
    }

    fn wake_cpus_up(&self) -> Result<(), &'static str> {
        let psci_node = self
            .device_tree
            .root()
            .find_child("psci")
            .ok_or(err_msg!("could not find psci"))?;

        let method = psci_node
            .get_property("method")
            .ok_or(err_msg!("could not find method"))?;

        let psci_inst = match method.value() {
            PropertyValue::String(m) => psci::new(m).or(Err(err_msg!("failed to create PSCI")))?,
            _ => return Err(err_msg!("invalid PSCI method")),
        };

        let cpus = self
            .device_tree
            .root()
            .find_child("cpus")
            .ok_or(err_msg!("could not find cpus"))?;

        let cpu_map = cpus
            .find_child("cpu-map")
            .ok_or(err_msg!("could not find cpu-map"))?;

        let mut aff2_max = 1;
        let mut aff1_max = 1;
        let mut aff0_max = 1;
        for socket in cpu_map
            .nodes()
            .iter()
            .filter(|n| n.name().starts_with("socket"))
        {
            let (_, aff2_str) = socket.name().split_at("socket".len());
            let aff2 =
                u64::from_str_radix(aff2_str, 10).or(Err(err_msg!("invalid socket number")))?;

            aff2_max = aff2_max.max(aff2);

            for cluster in socket
                .nodes()
                .iter()
                .filter(|n| n.name().starts_with("cluster"))
            {
                let (_, aff1_str) = cluster.name().split_at("cluster".len());
                let aff1 = u64::from_str_radix(aff1_str, 10)
                    .or(Err(err_msg!("invalid cluster number")))?;

                aff1_max = aff1_max.max(aff1);

                for core in cluster
                    .nodes()
                    .iter()
                    .filter(|n| n.name().starts_with("core"))
                {
                    let (_, aff0_str) = core.name().split_at("core".len());
                    let aff0 = u64::from_str_radix(aff0_str, 10)
                        .or(Err(err_msg!("invalid core number")))?;

                    aff0_max = aff0_max.max(aff0);
                    log::debug!("aff0 = {aff0}");

                    match (aff0, aff1, aff2) {
                        (0, 0, 0) => (),
                        _ => {
                            let affinity = Affinity::new(aff0, aff1, aff2, 0);
                            psci_inst
                                .cpu_on(affinity, get_kernel_start() as usize)
                                .or(Err(err_msg!("failed to a boot non-primary CPU")))?;
                        }
                    }
                }
            }
        }

        unsafe { set_max_affinity(aff0_max, aff1_max, aff2_max, 1) };

        Ok(())
    }
}
