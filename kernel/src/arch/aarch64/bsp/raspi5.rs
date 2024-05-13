use super::{DeviceTreeNodeRef, DeviceTreeRef, StaticArrayedNode};

use crate::arch::aarch64::bsp::raspi5::uart::unsafe_puts;
use crate::arch::aarch64::vm::VM;
use crate::arch::aarch64::vm;
use crate::config::DMA_SIZE;

use awkernel_drivers::raspi5::*;
use awkernel_drivers::{
    ic::{
        self,
        raspi::dma::{Dma, MEM_FLAG_DIRECT},
    },
};

use awkernel_lib::console::register_unsafe_puts;
use awkernel_lib::console::unsafe_print_hex_u64;
use awkernel_lib::err_msg;
use awkernel_lib::device_tree::prop::Range;
use awkernel_lib::device_tree::prop::PropertyValue;
use awkernel_lib::device_tree::traits::HasNamedChildNode;
use awkernel_lib::addr::phy_addr::PhyAddr;
use awkernel_lib::addr::virt_addr::VirtAddr;
use awkernel_lib::addr::Addr;
use awkernel_lib::paging::PAGESIZE;

pub mod config;
mod pciebridge;
mod uart;

pub struct Raspi5 {
    symbols: Option<DeviceTreeNodeRef>,
    device_tree: DeviceTreeRef,
    device_tree_base: usize,
    dma_pool: Option<VirtAddr>,
}

static mut DMA: Option<Dma> = None;

impl super::SoC for Raspi5 {
    unsafe fn init_device(&mut self) -> Result<(), &'static str> {
        self.init_symbols()
            .ok_or(err_msg!("failed to initialize __symbols__ node"))?;
        self.init_pcie_bridge();
        self.init_uart();
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

        if let Some(dma) =
            ic::raspi::dma::Dma::new(DMA_SIZE as u32, PAGESIZE as u32, MEM_FLAG_DIRECT)
        {
            let bus_addr = dma.get_bus_addr() as usize;
            let phy_addr = bus_addr & 0x3FFFFFFF;
            let start = PhyAddr::new(phy_addr);
            let end = PhyAddr::new(phy_addr + DMA_SIZE);

            let _ = vm.remove_heap(start, end);
            if vm.push_device_range(start, end).is_ok() {
                unsafe_puts("DMA: BUS address = ");
                unsafe_print_hex_u64(bus_addr as u64);
                unsafe_puts(", Physical address = ");
                unsafe_print_hex_u64(phy_addr as u64 & 0x3FFFFFFF);
                unsafe_puts("\r\n");

                self.dma_pool = Some(VirtAddr::new(start.as_usize()));

                unsafe {
                    DMA = Some(dma);
                }
            }
        };

        vm.print();

        unsafe_puts("init_vm_end.\r\n");

        Ok(vm)
    }

    unsafe fn init(&self) -> Result<(), &'static str> {
        Ok(())
    }
}

impl Raspi5 {
    pub const fn new(device_tree: DeviceTreeRef, device_tree_base: usize) -> Self {
        Raspi5 {
            symbols: None,
            device_tree,
            device_tree_base,
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
