use super::{DeviceTreeNodeRef, DeviceTreeRef, StaticArrayedNode};
use crate::{
    arch::aarch64::{
        interrupt_ctl,
        vm::{self, VM},
    },
    config::DMA_SIZE,
};
use alloc::{boxed::Box, format};
use awkernel_drivers::{
    hal::{self, raspi::uart::PinUart},
    ic::{
        self,
        raspi::dma::{Dma, MEM_FLAG_DIRECT},
    },
    uart::pl011::PL011,
};
use awkernel_lib::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    arch::aarch64::{armv8_timer::Armv8Timer, set_max_affinity},
    console::{register_console, register_unsafe_puts, unsafe_print_hex_u64, unsafe_puts},
    device_tree::{
        node::DeviceTreeNode,
        prop::{PropertyValue, Range},
        traits::HasNamedChildNode,
    },
    err_msg,
    net::ether::ETHER_ADDR_LEN,
    paging::PAGESIZE,
};
use core::{alloc::Allocator, arch::asm};

pub mod config;
pub mod memory;
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

pub struct Raspi {
    symbols: Option<DeviceTreeNodeRef>,
    interrupt: Option<StaticArrayedNode>,
    interrupt_compatible: &'static str,
    local_interrupt: Option<StaticArrayedNode>,
    local_interrupt_compatible: Option<&'static str>,
    device_tree: DeviceTreeRef,
    device_tree_base: usize,
    uart_base: Option<usize>,
    uart_irq: Option<u16>,
    dma_pool: Option<VirtAddr>,
}

static mut DMA: Option<Dma> = None;

impl super::SoC for Raspi {
    unsafe fn init_device(&mut self) -> Result<(), &'static str> {
        self.init_symbols()
            .ok_or(err_msg!("failed to initialize __symbols__ node"))?;
        self.init_interrupt_fields()?;
        self.init_uart0()?;
        self.init_mbox()?;
        self.init_framebuffer();

        set_max_affinity(4, 0, 0, 0);

        start_non_primary();

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
        self.init_timer()?;
        self.init_gpio()?;
        self.init_i2c()?;
        self.init_clock()?;
        self.init_spi()?;
        self.init_pwm()?;
        self.init_uarts();

        let _ = self.init_ethernet();

        Ok(())
    }

    fn get_dma_pool(&self, segment: usize) -> Option<VirtAddr> {
        if segment == 0 {
            self.dma_pool
        } else {
            None
        }
    }

    fn get_num_cpus(&self) -> usize {
        self.device_tree.num_cpus().unwrap_or(4)
    }
}

impl Raspi {
    pub const fn new(device_tree: DeviceTreeRef, device_tree_base: usize) -> Self {
        Raspi {
            symbols: None,
            interrupt: None,
            interrupt_compatible: "",
            local_interrupt: None,
            local_interrupt_compatible: None,
            device_tree,
            device_tree_base,
            uart_base: None,
            uart_irq: None,
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

    fn init_interrupt_fields(&mut self) -> Result<(), &'static str> {
        let intc = self
            .get_device_from_symbols("gicv2")
            .or(self.get_device_from_symbols("intc"))
            .or(Err(err_msg!("failed to get the interrupt node")))?;

        let leaf = intc.get_leaf_node().unwrap();

        let compatible_prop = leaf
            .get_property("compatible")
            .ok_or(err_msg!("interrupt node has no compatible property"))?;

        self.interrupt_compatible = match compatible_prop.value() {
            PropertyValue::String(s) => s,
            _ => {
                return Err(err_msg!(
                    "compatible property of interrupt has not string value"
                ))
            }
        };

        if let Ok(local_intc) = self.get_device_from_symbols("local_intc") {
            let local_compat_prop = local_intc.get_leaf_node().unwrap();
            let prop = local_compat_prop
                .get_property("compatible")
                .ok_or(err_msg!("local_intc node has no compatible property"))?;

            self.local_interrupt_compatible = match prop.value() {
                PropertyValue::String(s) => Some(s),
                _ => {
                    return Err(err_msg!(
                        "compatible property of local_intc has not string value"
                    ))
                }
            };

            self.local_interrupt = Some(local_intc);
        }

        self.interrupt = Some(intc);

        Ok(())
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

    fn get_irq<A>(&self, node: &DeviceTreeNode<A>, n: usize) -> Result<u16, &'static str>
    where
        A: Allocator + Clone,
    {
        // Get IRQ#.
        let Some(interrupts_prop) = node.get_property("interrupts") else {
            return Err(err_msg!("could not find interrupts property"));
        };

        let PropertyValue::Integers(interrupts) = interrupts_prop.value() else {
            return Err(err_msg!("interrupts property has invalid value"));
        };

        let index = n * 3;

        if index >= interrupts.len() {
            return Err(err_msg!("interrupts property has not enough elements"));
        }

        let interrupts = &interrupts[index..index + 3];

        let irq = interrupt_ctl::get_irq(self.interrupt_compatible, interrupts)
            .ok_or(err_msg!("failed to get IRQ# from the interrupt controller"))?;

        Ok(irq)
    }

    fn init_uarts(&self) {
        unsafe { hal::raspi::uart::set_uart_clock(super::config::UART_CLOCK) };

        // Raspberry Pi 4 has 5 UARTs.
        for i in 2..=5 {
            let Ok(uart_arrayed_node) = self.get_device_from_symbols(&format!("uart{}", i)) else {
                continue;
            };

            // Get the base address.
            let Ok(base_addr) = uart_arrayed_node.get_address(0) else {
                continue;
            };

            let uart_node = uart_arrayed_node.get_leaf_node().unwrap();

            // Get IRQ#.
            let Ok(irq) = self.get_irq(uart_node, 0) else {
                continue;
            };

            // The compatible property must be "arm,pl011".
            if !uart_node.compatible(&["arm,pl011"]) {
                continue;
            }

            let Ok(pins_arrayed_node) = self.get_device_from_symbols(&format!("uart{}_pins", i))
            else {
                continue;
            };

            let Some(pins_node) = pins_arrayed_node.get_leaf_node() else {
                continue;
            };

            // Get the brcm,pins property.
            let Some(pins) = pins_node.get_property("brcm,pins") else {
                continue;
            };

            let (tx_gpio, rx_gpio) = match pins.value() {
                PropertyValue::Integers(v) => {
                    if v.len() != 2 {
                        continue;
                    }
                    (v[0], v[1])
                }
                _ => continue,
            };

            // Get the brcm,function property.
            let Some(function) = pins_node.get_property("brcm,function") else {
                continue;
            };
            let alt = match function.value() {
                PropertyValue::Integer(v) => hal::raspi::gpio::GpioFunction::from(*v as u32),
                _ => continue,
            };

            // Get the brcm,pull property.
            let Some(pull_mode) = pins_node.get_property("brcm,pull") else {
                continue;
            };
            let (tx_pull, rx_pull) = match pull_mode.value() {
                PropertyValue::Integers(v) => {
                    if v.len() != 2 {
                        continue;
                    }
                    let tx_pull = hal::raspi::gpio::PullMode::from(v[0] as u32);
                    let rx_pull = hal::raspi::gpio::PullMode::from(v[1] as u32);
                    (tx_pull, rx_pull)
                }
                _ => continue,
            };

            let tx = hal::raspi::uart::Pin::new(tx_gpio as u32, alt, tx_pull);
            let rx = hal::raspi::uart::Pin::new(rx_gpio as u32, alt, rx_pull);

            let uarts = hal::raspi::uart::Uarts::from(i);
            let pin_uart = PinUart::new(tx, rx, irq, base_addr as usize);

            unsafe { hal::raspi::uart::set_uart_info(uarts, pin_uart) };
        }
    }

    fn init_uart0(&mut self) -> Result<(), &'static str> {
        let uart0_arrayed_node = self
            .get_device_from_symbols("uart0")
            .or(Err(err_msg!("could not find uart0")))?;

        // Get the base address.
        let uart_base = uart0_arrayed_node
            .get_address(0)
            .or(Err(err_msg!("failed to calculate uart0's base address")))?;

        let uart0_node = uart0_arrayed_node.get_leaf_node().unwrap();

        // The compatible property must be "arm,pl011".
        if !uart0_node.compatible(&["arm,pl011"]) {
            return Err(err_msg!("uart0 is not PL011"));
        }

        let interrupts_prop = uart0_node
            .get_property("interrupts")
            .ok_or(err_msg!("uart0 has no interrupt property"))?;

        let interrupts = match interrupts_prop.value() {
            PropertyValue::Integers(ints) => ints,
            _ => {
                return Err(err_msg!(
                    "uart0's compatible property is not a integer vector"
                ))
            }
        };

        let irq = interrupt_ctl::get_irq(self.interrupt_compatible, interrupts)
            .ok_or(err_msg!("failed to get UART0's IRQ#"))?;

        let gpio_arrayed_node = self.get_device_from_symbols("gpio")?;
        let gpio_base = gpio_arrayed_node
            .get_address(0)
            .or(Err(err_msg!("failed to get GPIO's base address")))?;

        uart::init(uart_base as usize, gpio_base as usize, irq);

        self.uart_base = Some(uart_base as usize);
        self.uart_irq = Some(irq);

        register_unsafe_puts(uart::unsafe_puts);

        unsafe { unsafe_puts("uart0 has been successfully initialized.\r\n") };

        Ok(())
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

    fn init_interrupt_controller(&self) -> Result<(), &'static str> {
        let Some(intc) = &self.interrupt else {
            return Err(err_msg!("interrupt is not initialized"));
        };

        interrupt_ctl::init_interrupt_controller(
            self.interrupt_compatible,
            intc,
            self.local_interrupt_compatible,
            self.local_interrupt.as_ref(),
        )
    }

    fn init_gpio(&self) -> Result<(), &'static str> {
        let gpio_node = self.get_device_from_symbols("gpio")?;
        let base_addr = gpio_node
            .get_address(0)
            .or(Err(err_msg!("could not find GPIO's base address")))?;

        log::info!("GPIO: 0x{base_addr:016x}");

        unsafe { awkernel_drivers::hal::raspi::gpio::set_gpio_base(base_addr as usize) };

        Ok(())
    }

    fn init_i2c(&self) -> Result<(), &'static str> {
        let i2c_node = self
            .get_device_from_symbols("i2c1")
            .or(Err(err_msg!("could not find I2C's device node")))?;
        let base_addr = i2c_node
            .get_address(0)
            .or(Err(err_msg!("could not find I2C's base address")))?;

        log::info!("I2C: 0x{base_addr:016x}");

        unsafe { awkernel_drivers::hal::raspi::i2c::set_i2c_base(base_addr as usize) };

        Ok(())
    }

    fn init_mbox(&self) -> Result<(), &'static str> {
        let mbox_node = self
            .get_device_from_symbols("mailbox")
            .or(Err(err_msg!("could not find Mbox's device node")))?;
        let base_addr = mbox_node
            .get_address(0)
            .or(Err(err_msg!("could not find Mbox's base address")))?;

        unsafe { awkernel_drivers::ic::raspi::mbox::set_mbox_base(base_addr as usize) };

        Ok(())
    }

    pub fn init_clock(&self) -> Result<(), &'static str> {
        let clk_node = self
            .get_device_from_symbols("clocks")
            .or(Err(err_msg!("could not find CLK's device node")))?;
        let base_addr = clk_node
            .get_address(0)
            .or(Err(err_msg!("could not find clk's base address")))?;

        log::info!("CLK: 0x{:016x}", base_addr);

        let clocks_node = self
            .device_tree
            .root()
            .find_child("clocks")
            .ok_or(err_msg!("could not find 'clocks' node"))?;

        let osc_node = clocks_node.find_child("clk-osc").ok_or(err_msg!(
            "could not find 'clk-osc' node under 'clocks' node"
        ))?;

        let clock_freq_prop = osc_node.get_property("clock-frequency").ok_or(err_msg!(
            "could not find 'clock-frequency' property in 'clk-osc' node"
        ))?;

        let clock_freq = match clock_freq_prop.value() {
            PropertyValue::Integer(value) => {
                log::info!("CLK-OSC clock-frequency: {} Hz", value);
                *value
            }
            _ => {
                log::error!("'clock-frequency' property has an invalid type");
                return Err("'clock-frequency' property has an invalid type");
            }
        };
        unsafe { hal::raspi::clock::set_clock_frequency(clock_freq as usize) };

        unsafe { hal::raspi::clock::set_clk_base(base_addr as usize) };

        Ok(())
    }

    fn init_spi(&self) -> Result<(), &'static str> {
        let spi_node = self
            .get_device_from_symbols("spi")
            .or(Err(err_msg!("could not find SPI's device node")))?;
        let base_addr = spi_node
            .get_address(0)
            .or(Err(err_msg!("could not find SPI's base address")))?;

        log::info!("SPI: 0x{:016x}", base_addr);

        unsafe { hal::raspi::spi::set_spi_base(base_addr as usize) };

        Ok(())
    }

    fn init_pwm(&self) -> Result<(), &'static str> {
        let spi_node = self
            .get_device_from_symbols("pwm")
            .or(Err(err_msg!("could not find PWM's device node")))?;
        let base_addr = spi_node
            .get_address(0)
            .or(Err(err_msg!("could not find PWM's base address")))?;

        log::info!("PWM: 0x{:016x}", base_addr);

        unsafe { hal::raspi::pwm::set_pwm_base(base_addr as usize) };

        Ok(())
    }

    fn init_timer(&self) -> Result<(), &'static str> {
        let timer_node = self
            .device_tree
            .root()
            .find_child("timer")
            .ok_or(err_msg!("could not find timer"))?;

        if timer_node.compatible(&["arm,armv8-timer"]) {
            // IRQ #27 is the recommended value.
            let timer = Box::new(Armv8Timer::new(27));

            awkernel_lib::timer::register_timer(timer);

            log::info!("armv8-timer has been initialized.");
        }

        // Timer of Raspberry Pi 3 is not supported.

        Ok(())
    }

    fn init_framebuffer(&self) {
        unsafe {
            if ic::raspi::lfb::lfb_init(640, 360).is_err() {
                unsafe_puts("Failed to initialize the linear framebuffer.\r\n");
            }
        }
    }

    /// Initialize the Ethernet controller.
    fn init_ethernet(&self) -> Result<(), &'static str> {
        let Ok(node) = self.get_device_from_symbols("genet") else {
            return Err(err_msg!("could not find the Ethernet controller"));
        };

        let leaf = node
            .get_leaf_node()
            .ok_or(err_msg!("genet node has no leaf node"))?;

        // The compatible property must be "brcm,bcm2711-genet-v5" or "brcm,genet-v5".
        if !leaf.compatible(&["brcm,bcm2711-genet-v5", "brcm,genet-v5"]) {
            return Err(err_msg!("unsupported Ethernet controller"));
        }

        // Get the base address.
        let base_addr = node
            .get_address(0)
            .or(Err(err_msg!("could not find the base address")))?;

        // Get IRQ#s.
        let irq0 = self.get_irq(leaf, 0)?;
        let irq1 = self.get_irq(leaf, 1)?;

        // Get the phy-mode property.
        let Some(phy_mode_prop) = leaf.get_property("phy-mode") else {
            return Err(err_msg!("could not find the phy-mode property"));
        };

        let phy_mode = match phy_mode_prop.value() {
            PropertyValue::String(s) => s,
            _ => return Err(err_msg!("phy-mode property has invalid value")),
        };

        // Get the local-mac-address property.
        let mac_addr = if let Some(prop) = leaf.get_property("local-mac-address") {
            let val = prop.raw_value();
            if val.len() == ETHER_ADDR_LEN {
                Some([val[0], val[1], val[2], val[3], val[4], val[5]])
            } else {
                None
            }
        } else {
            None
        };

        fn get_phy_id<A>(node: &DeviceTreeNode<A>) -> Option<u32>
        where
            A: Allocator + Clone,
        {
            // Get the phy-handle property.
            let prop = node.get_property("phy-handle")?;

            let phandle = match prop.value() {
                PropertyValue::PHandle(p) => *p,
                PropertyValue::Integer(p) => *p as u32,
                _ => return None,
            };

            let node_phandle = node.get_node_by_phandle(phandle)?;
            let prop = node_phandle.get_property("reg")?;

            match prop.value() {
                PropertyValue::Address(addr0, _) => {
                    let addr = addr0.to_u128() as u32;
                    Some(addr)
                }
                _ => None,
            }
        }

        let phy_id = get_phy_id(leaf);

        log::info!(
            "GENET: base_addr = 0x{:016x}, irq0 = {irq0}, irq1 = {irq1}, phy_mode = {phy_mode}, mac_addr = {mac_addr:02x?}, phy_id = {phy_id:x?}",
            base_addr
        );

        if let Err(e) = awkernel_drivers::ic::genet::attach(
            VirtAddr::new(base_addr as usize),
            &[irq0, irq1],
            phy_mode,
            phy_id,
            &mac_addr,
        ) {
            log::error!("Failed to initialize GENET: {:?}", e);
        }

        Ok(())
    }
}
