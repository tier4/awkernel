use super::{DeviceTreeNodeRef, DeviceTreeRef, StaticArrayedNode};

use crate::{
    arch::aarch64::vm::{self, MemoryRange, VM},
    config::DMA_SIZE,
};

use awkernel_drivers::pcie::pcie_device_tree::PCIeRange;

use alloc::vec::Vec;

use awkernel_drivers::raspi5::*;

use awkernel_lib::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    console::{register_unsafe_puts, unsafe_puts},
    device_tree::{
        prop::{PropertyValue, Range},
        traits::HasNamedChildNode,
    },
    err_msg,
    paging::PAGESIZE,
};

pub mod config;
mod pciebridge;
mod uart;

pub struct Raspi5 {
    symbols: Option<DeviceTreeNodeRef>,
    device_tree: DeviceTreeRef,
    device_tree_base: usize,
    pcie_reg: Option<(PhyAddr, usize)>,
    dma_pool: Option<VirtAddr>,
}

impl super::SoC for Raspi5 {
    unsafe fn init_device(&mut self) -> Result<(), &'static str> {
        self.init_symbols()
            .ok_or(err_msg!("failed to initialize __symbols__ node"))?;
        self.init_pcie_bridge();
        self.init_uart();
        let _ = self.get_pcie_mem();
        self.init_gpio();
        Ok(())
    }

    unsafe fn init_virtual_memory(&mut self) -> Result<VM, &'static str> {
        let mut vm = VM::new();

        let num_cpus = self
            .device_tree
            .num_cpus()
            .or(Err(err_msg!("failed to get num_cpus")))?;
        vm.set_num_cpus(num_cpus);

        // Device memory regions.
        let ranges = self.device_ranges()?;
        for range in ranges {
            let start = range.range.1.to_u128() as usize;
            let end = start + range.range.2.to_u128() as usize;
            vm.push_device_range(PhyAddr::new(start), PhyAddr::new(end))?;
        }

        if let Some((start, size)) = awkernel_drivers::ic::raspi::lfb::get_frame_buffer_region() {
            vm.push_device_range(PhyAddr::new(start), PhyAddr::new(start + size))?;
        }

        // PCIe regions.
        if let Some((base, size)) = self.pcie_reg {
            vm.push_device_range(base, base + size)?;
        }

        // Add heap memory regions.
        vm.add_heap_from_node(self.device_tree.root())?;

        // Do not use the memory containing kernel's binary for heap memory.
        vm.remove_kernel_memory_from_heap_memory()?;

        let mask = PAGESIZE - 1;
        let device_tree_start = self.device_tree_base & !mask;
        let end = self.device_tree_base + self.device_tree.total_size();
        let end = end + PAGESIZE - (end & mask);

        vm.remove_heap(PhyAddr::new(device_tree_start), PhyAddr::new(end))?; // Do not use DTB's memory region for heap memory.
        vm.push_ro_memory(PhyAddr::new(device_tree_start), PhyAddr::new(end))?; // Make DTB's memory region read-only memory.

        let _ = vm.remove_heap(
            PhyAddr::new(0),
            PhyAddr::new(vm::get_kernel_start() as usize),
        );

        // Allocate a memory region for the DMA pool.
        if let Some(dma_start) = vm.find_heap(
            DMA_SIZE,
            MemoryRange::new(PhyAddr::new(0), PhyAddr::new(!0)),
        ) {
            let dma_end = dma_start + DMA_SIZE;
            vm.remove_heap(dma_start, dma_end)?;
            vm.push_device_range(dma_start, dma_end)?;
            self.dma_pool = Some(VirtAddr::new(dma_start.as_usize()));
        }

        vm.print();

        unsafe_puts("Initializing the page table. Wait a moment.\r\n");

        vm.init()?;

        Ok(vm)
    }

    unsafe fn init(&self) -> Result<(), &'static str> {
        if let Err(msg) = self.init_pcie() {
            log::warn!("failed to initialize PCIe: {}", msg);
        }

        Ok(())
    }

    fn get_num_cpus(&self) -> usize {
        self.device_tree.num_cpus().unwrap_or(4)
    }
}

impl Raspi5 {
    pub const fn new(device_tree: DeviceTreeRef, device_tree_base: usize) -> Self {
        Raspi5 {
            symbols: None,
            device_tree,
            device_tree_base,
            pcie_reg: None,
            dma_pool: None,
        }
    }

    /// Find "__symbols__" node and initialize `ALIASES_NODE` by the node.
    fn init_symbols(&mut self) -> Option<()> {
        // Find "aliases" node.
        let symbols = self.device_tree.root().find_child("__symbols__")?;

        self.symbols = Some(symbols);

        Some(())
    }

    fn device_ranges(&self) -> Result<&[Range], &'static str> {
        let soc = self
            .get_device_from_symbols("soc")?
            .get_leaf_node()
            .unwrap();

        let ranges_prop = soc
            .get_property("ranges")
            .ok_or(err_msg!("could not find ranges property"))?;

        let ranges = match ranges_prop.value() {
            PropertyValue::Ranges(r) => r,
            _ => return Err(err_msg!("ranges property has invalid value")),
        };

        Ok(ranges)
    }

    /// If `name = "/soc/serial"`,
    /// then `Some([Some(root node), Some(soc node), Some(serial node), None, ...])`
    /// will be returned.
    ///
    /// If there is no such node, `None` will be returned.
    fn get_device_from_symbols(&self, name: &str) -> Result<StaticArrayedNode, &'static str> {
        let Some(symbols) = self.symbols.as_ref() else {
            return Err(err_msg!("the symbols node has not been initialized"));
        };

        let alias = symbols
            .get_property(name)
            .ok_or(err_msg!("could not find such property"))?;

        let abs_path = match alias.value() {
            PropertyValue::String(p) => *p,
            _ => return Err(err_msg!("__symbols__ is not a string")),
        };

        self.device_tree
            .root()
            .get_arrayed_node(abs_path)
            .or(Err(err_msg!("invalid path")))
    }

    unsafe fn get_pcie_mem(&mut self) -> Result<(), &'static str> {
        // Find PCIe node.
        let pcie_node = if let Some(axi) = self.device_tree.root().find_child("axi") {
            axi.nodes().iter().find(|n| {
                let name = n.name();
                name.starts_with("pcie@120000")
            })
        } else {
            None
        };

        // Get the "reg" property.
        if let Some(pcie_node) = pcie_node {
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
        } else {
            Err(err_msg!("PCIe: node not found"))
        }
    }

    fn init_pcie(&self) -> Result<(), &'static str> {
        let pcie_node = if let Some(axi) = self.device_tree.root().find_child("axi") {
            // Try to find the `pcie@` node within `axi`
            axi.nodes().iter().find(|n| {
                let name = n.name();
                name.starts_with("pcie@120000") // Check if the node name starts with "pcie@"
            })
        } else {
            // If the `axi` node is not found, return None
            None
        };

        // Get the "ranges" property.
        if let Some(pcie_node) = pcie_node {
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

            for i in (0..).step_by(56) {
                if i + 56 > value.len() {
                    break;
                }
                let slice = &value[i..i + 56];

                let head = u32::from_be_bytes([slice[0], slice[1], slice[2], slice[3]]);
                let pcie_addr =
                    ((u32::from_be_bytes([slice[4], slice[5], slice[6], slice[7]]) as u64) << 32)
                        | u32::from_be_bytes([slice[8], slice[9], slice[10], slice[11]]) as u64;
                let cpu_addr = ((u32::from_be_bytes([slice[12], slice[13], slice[14], slice[15]])
                    as u64)
                    << 32)
                    | u32::from_be_bytes([slice[16], slice[17], slice[18], slice[19]]) as u64;
                let size = ((u32::from_be_bytes([slice[20], slice[21], slice[22], slice[23]])
                    as u64)
                    << 32)
                    | u32::from_be_bytes([slice[24], slice[25], slice[26], slice[27]]) as u64;

                let range =
                    PCIeRange::new(head, pcie_addr as usize, cpu_addr as usize, size as usize);
                ranges.push(range);
            }

            // Get the "reg" property.
            let Some((base, _size)) = self.pcie_reg else {
                return Err(err_msg!("PCIe: PCIe registers are not initialized"));
            };

            // Initialize PCIe.
            awkernel_drivers::pcie::init_with_addr(
                0,
                VirtAddr::new(base.as_usize()),
                Some(ranges.as_mut_slice()),
                0,
                2,
            );

            unsafe {
                unsafe_puts("PCIe has been successfully initialized.\r\n");
            }

            Ok(())
        } else {
            unsafe {
                unsafe_puts("PCIe: node not found\r\n");
            }
            Ok(())
        }
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
