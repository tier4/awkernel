use alloc::{boxed::Box, vec::Vec};
use awkernel_drivers::{
    pcie::pcie_device_tree::PCIeRange,
    psci::{self, Affinity},
    uart::pl011::PL011,
};
use awkernel_lib::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    arch::aarch64::set_max_affinity,
    console::register_console,
    device_tree::{prop::PropertyValue, traits::HasNamedChildNode},
    err_msg,
    paging::PAGESIZE,
};

use crate::arch::aarch64::{
    bsp::aarch64_virt::uart::unsafe_puts,
    interrupt_ctl,
    vm::{get_kernel_start, VM},
};

use super::{DeviceTreeRef, StaticArrayedNode};

pub mod config;
mod uart;

const DEVICE_MEM_START: PhyAddr = PhyAddr::new(0x0800_0000);
const DEVICE_MEM_END: PhyAddr = PhyAddr::new(0x4000_0000);
const FLASH_START: PhyAddr = PhyAddr::new(0);
const FLASH_END: PhyAddr = PhyAddr::new(0x0800_0000);

pub struct AArch64Virt {
    device_tree: DeviceTreeRef,
    device_tree_base: PhyAddr,
    uart_base: Option<usize>,
    uart_irq: Option<u16>,
    interrupt: Option<StaticArrayedNode>,
    interrupt_compatible: &'static str,
    pcie_reg: Option<(PhyAddr, usize)>,
}

impl super::SoC for AArch64Virt {
    unsafe fn init_device(&mut self) -> Result<(), &'static str> {
        self.init_interrupt_fields()?;
        self.init_uart()?;
        awkernel_lib::device_tree::print_device_tree_node(self.device_tree.root(), 0);

        if let Err(err) = self.wake_cpus_up() {
            unsafe_puts(err);
            unsafe_puts("\r\n");
            return Err(err);
        }

        if let Err(msg) = self.get_pcie_mem() {
            unsafe_puts(msg);
            unsafe_puts("\r\n");
        }

        Ok(())
    }

    unsafe fn init_virtual_memory(&self) -> Result<crate::arch::aarch64::vm::VM, &'static str> {
        let mut vm = VM::new();

        // Add PCIe's configuration space.
        if let Some((base, size)) = self.pcie_reg {
            vm.push_device_range(base, base + size)?;
        }

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

        let mask = PhyAddr::new(PAGESIZE - 1);
        let start = self.device_tree_base & !mask;
        let end = self.device_tree_base + PhyAddr::new(self.device_tree.total_size());
        let end = end + PhyAddr::new(PAGESIZE) - (end & mask);

        vm.remove_heap(start, end)?; // Do not use DTB's memory region for heap memory.
        vm.push_ro_memory(start, end)?; // Make DTB's memory region read-only memory.

        vm.print();
        unsafe_puts("Initializing the page table. Wait a moment.\r\n");

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

        if let Err(msg) = self.init_pcie() {
            log::warn!("failed to initialize PCIe: {}", msg);
        }

        Ok(())
    }
}

impl AArch64Virt {
    pub fn new(device_tree: DeviceTreeRef, device_tree_base: usize) -> Self {
        AArch64Virt {
            device_tree,
            device_tree_base: PhyAddr::new(device_tree_base),
            uart_base: None,
            uart_irq: None,
            interrupt: None,
            interrupt_compatible: "",
            pcie_reg: None,
        }
    }

    unsafe fn get_pcie_mem(&mut self) -> Result<(), &'static str> {
        // Find PCIe node.
        let Some(pcie_node) = self
            .device_tree
            .root()
            .nodes()
            .iter()
            .find(|n| n.name().starts_with("pcie@"))
        else {
            return Ok(());
        };

        unsafe_puts("PCIe node found.\r\n");

        // Get the "reg" property.
        let reg_prop = pcie_node
            .get_property("reg")
            .ok_or(err_msg!("PCIe: failed to get reg property"))?;

        let reg = match reg_prop.value() {
            PropertyValue::Address(base, size) => (base, size),
            _ => return Err(err_msg!("PCIe: reg property has invalid value")),
        };

        let reg_base = reg.0.to_u128() as usize;
        let reg_size = reg.1.to_u128() as usize;

        let pcie_regs = (PhyAddr::new(reg_base), reg_size);

        self.pcie_reg = Some(pcie_regs);

        Ok(())
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
                clocks.first().ok_or(err_msg!("clocks has invalid value"))?
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

        interrupt_ctl::init_interrupt_controller(self.interrupt_compatible, intc, None, None)
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
            let aff2 = aff2_str
                .parse::<u64>()
                .or(Err(err_msg!("invalid socket number")))?;

            aff2_max = aff2_max.max(aff2);

            for cluster in socket
                .nodes()
                .iter()
                .filter(|n| n.name().starts_with("cluster"))
            {
                let (_, aff1_str) = cluster.name().split_at("cluster".len());
                let aff1 = aff1_str
                    .parse::<u64>()
                    .or(Err(err_msg!("invalid cluster number")))?;

                aff1_max = aff1_max.max(aff1);

                for core in cluster
                    .nodes()
                    .iter()
                    .filter(|n| n.name().starts_with("core"))
                {
                    let (_, aff0_str) = core.name().split_at("core".len());
                    let aff0 = aff0_str
                        .parse::<u64>()
                        .or(Err(err_msg!("invalid core number")))?;

                    aff0_max = aff0_max.max(aff0);

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

    fn init_pcie(&self) -> Result<(), &'static str> {
        // Find PCIe node.
        let Some(pcie_node) = self
            .device_tree
            .root()
            .nodes()
            .iter()
            .find(|n| n.name().starts_with("pcie@"))
        else {
            return Err(err_msg!("PCIe node not found"));
        };

        // Get the "ranges" property.
        let ranges_prop = pcie_node
            .get_property("ranges")
            .ok_or(err_msg!("PCIe: failed to get ranges property"))?;

        if !matches!(ranges_prop.value(), PropertyValue::Ranges(_)) {
            return Err(err_msg!("PCIe: ranges property has invalid value"));
        };

        let value = ranges_prop.raw_value();

        if value.len() % 28 != 0 {
            return Err(err_msg!("PCIe: ranges property has invalid length"));
        }

        let mut ranges = Vec::new();

        // A range's format:
        // {
        //     head: u32,
        //     pcie_mem_hi: u32,
        //     pcie_mem_lo: u32,
        //     cpu_mem_hi: u32,
        //     cpu_mem_lo: u32,
        //     size_hi: u32,
        //     size_lo: u32,
        // }
        //
        // `head`'s format is described in the following link.
        // https://elinux.org/Device_Tree_Usage#PCI_Address_Translation
        for i in (0..).step_by(28) {
            if i >= value.len() {
                break;
            }

            let value = &value[i..(i + 28)];

            let head = u32::from_be_bytes([value[0], value[1], value[2], value[3]]);
            let pcie_mem_hi = u32::from_be_bytes([value[4], value[5], value[6], value[7]]);
            let pcie_mem_lo = u32::from_be_bytes([value[8], value[9], value[10], value[11]]);
            let cpu_mem_hi = u32::from_be_bytes([value[12], value[13], value[14], value[15]]);
            let cpu_mem_lo = u32::from_be_bytes([value[16], value[17], value[18], value[19]]);
            let size_hi = u32::from_be_bytes([value[20], value[21], value[22], value[23]]);
            let size_lo = u32::from_be_bytes([value[24], value[25], value[26], value[27]]);

            let pcie_mem = (pcie_mem_hi as u64) << 32 | pcie_mem_lo as u64;
            let cpu_mem = (cpu_mem_hi as u64) << 32 | cpu_mem_lo as u64;
            let size = (size_hi as u64) << 32 | size_lo as u64;

            let range = PCIeRange::new(head, pcie_mem as usize, cpu_mem as usize, size as usize);
            ranges.push(range);
        }

        // Get the "reg" property.
        let Some((base, _size)) = self.pcie_reg else {
            return Err(err_msg!("PCIe: PCIe registers are not initialized"));
        };

        // TODO: disabled PCIe currently.

        // Initialize PCIe.
        // awkernel_drivers::pcie::init_with_addr(
        //     0,
        //     VirtAddr::new(base.as_usize()),
        //     ranges.as_slice(),
        // );

        Ok(())
    }
}
