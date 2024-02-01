use super::{DeviceTreeNodeRef, DeviceTreeRef, StaticArrayedNode};
use crate::arch::aarch64::{
    interrupt_ctl,
    vm::{self, VM},
};
use alloc::{boxed::Box, format};
use awkernel_drivers::{
    hal::{
        self,
        rpi::{self, uart::PinUart},
    },
    uart::pl011::PL011,
};
use awkernel_lib::{
    addr::phy_addr::PhyAddr,
    arch::aarch64::{armv8_timer::Armv8Timer, rpi_system_timer::RpiSystemTimer, set_max_affinity},
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
pub mod memory;
mod uart;

/// IRQ #27 is the recommended value.
/// every 1/2^19 = .000_001_9 [s].
pub static TIMER_ARM_V8: Armv8Timer = Armv8Timer::new(27, 19);

/// Because the device tree does not contain the system timer,
/// it is initialized with constant values,
/// IRQ #1 and the base address of 0x3f003000.
///
/// 64 is the offset for IRQ 1 / IRQ 2 of bcm2835's device driver.
pub static TIMER_RPI: RpiSystemTimer = RpiSystemTimer::new(1 + 64, 0x3f003000);

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
}

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

    unsafe fn init_virtual_memory(&self) -> Result<VM, &'static str> {
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

        if let Some((start, size)) =
            awkernel_drivers::framebuffer::rpi::lfb::get_frame_buffer_region()
        {
            vm.push_device_range(PhyAddr::new(start), PhyAddr::new(start + size))?;
        }

        // Add heap memory regions.
        vm.add_heap_from_node(self.device_tree.root())?;

        // Do not use the memory containing kernel's binary for heap memory.
        vm.remove_kernel_memory_from_heap_memory()?;

        let mask = PAGESIZE - 1;
        let start = self.device_tree_base & !mask;
        let end = self.device_tree_base + self.device_tree.total_size();
        let end = end + PAGESIZE - (end & mask);

        vm.remove_heap(PhyAddr::new(start), PhyAddr::new(end))?; // Do not use DTB's memory region for heap memory.
        vm.push_ro_memory(PhyAddr::new(start), PhyAddr::new(end))?; // Make DTB's memory region read-only memory.

        let _ = vm.remove_heap(
            PhyAddr::new(0),
            PhyAddr::new(vm::get_kernel_start() as usize),
        );

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

        Ok(())
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

    fn init_uarts(&self) {
        unsafe { hal::rpi::uart::set_uart_clock(super::config::UART_CLOCK) };

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
            let Some(interrupts_prop) = uart_node.get_property("interrupts") else {
                continue;
            };

            let interrupts = match interrupts_prop.value() {
                PropertyValue::Integers(ints) => ints,
                _ => continue,
            };

            let Some(irq) = interrupt_ctl::get_irq(self.interrupt_compatible, interrupts) else {
                continue;
            };

            // Get the compatible property.
            let Some(compatible_prop) = uart_node.get_property("compatible") else {
                continue;
            };

            let compatibles = match compatible_prop.value() {
                PropertyValue::Strings(v) => v,
                _ => continue,
            };

            // UART must be PL011.
            if !compatibles.iter().any(|c| *c == "arm,pl011") {
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
                PropertyValue::Integer(v) => hal::rpi::gpio::GpioFunction::from(*v as u32),
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
                    let tx_pull = hal::rpi::gpio::PullMode::from(v[0] as u32);
                    let rx_pull = hal::rpi::gpio::PullMode::from(v[1] as u32);
                    (tx_pull, rx_pull)
                }
                _ => continue,
            };

            let tx = hal::rpi::uart::Pin::new(tx_gpio as u32, alt, tx_pull);
            let rx = hal::rpi::uart::Pin::new(rx_gpio as u32, alt, rx_pull);

            let uarts = hal::rpi::uart::Uarts::from(i);
            let pin_uart = PinUart::new(tx, rx, irq, base_addr as usize);

            unsafe { hal::rpi::uart::set_uart_info(uarts, pin_uart) };
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

        // Get the compatible property.
        let compatible_prop = uart0_node
            .get_property("compatible")
            .ok_or(err_msg!("uart0 has no compatible property"))?;

        let compatibles = match compatible_prop.value() {
            PropertyValue::Strings(v) => v,
            _ => {
                return Err(err_msg!(
                    "uart0's compatible property is not a string vector"
                ))
            }
        };

        // UART0 must be PL011.
        compatibles
            .iter()
            .find(|c| **c == "arm,pl011")
            .ok_or(err_msg!("UART0 is not PL011"))?;

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

        unsafe { awkernel_drivers::hal::rpi::gpio::set_gpio_base(base_addr as usize) };

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

        unsafe { awkernel_drivers::hal::rpi::i2c::set_i2c_base(base_addr as usize) };

        Ok(())
    }

    fn init_mbox(&self) -> Result<(), &'static str> {
        let mbox_node = self
            .get_device_from_symbols("mailbox")
            .or(Err(err_msg!("could not find Mbox's device node")))?;
        let base_addr = mbox_node
            .get_address(0)
            .or(Err(err_msg!("could not find Mbox's base address")))?;

        unsafe { awkernel_drivers::framebuffer::rpi::mbox::set_mbox_base(base_addr as usize) };

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
        unsafe { rpi::clock::set_clock_frequency(clock_freq as usize) };

        unsafe { rpi::clock::set_clk_base(base_addr as usize) };

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

        unsafe { awkernel_drivers::hal::rpi::spi::set_spi_base(base_addr as usize) };

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

        unsafe { awkernel_drivers::hal::rpi::pwm::set_pwm_base(base_addr as usize) };

        Ok(())
    }

    fn init_timer(&self) -> Result<(), &'static str> {
        let timer_node = self
            .device_tree
            .root()
            .find_child("timer")
            .ok_or(err_msg!("could not find timer"))?;

        let prop = timer_node
            .get_property("compatible")
            .ok_or(err_msg!("could not find compatible property"))?;

        let compatible = match prop.value() {
            PropertyValue::String(s) => s,
            _ => return Err(err_msg!("")),
        };

        match *compatible {
            "arm,armv8-timer" => {
                log::info!("armv8-timer has been initialized.");
                awkernel_lib::timer::register_timer(&TIMER_ARM_V8);
            }
            _ => {
                awkernel_lib::timer::register_timer(&TIMER_RPI);
            }
        }

        Ok(())
    }

    fn init_framebuffer(&self) {
        unsafe {
            if awkernel_drivers::framebuffer::rpi::lfb::lfb_init(640, 360).is_err() {
                unsafe_puts("Failed to initialize the linear framebuffer.\r\n");
            }
        }
    }
}
