use super::{DeviceTreeNodeRef, DeviceTreeRef, StaticArrayedNode};
use crate::arch::aarch64::{
    interrupt_ctl,
    vm::{self, VM},
};
use alloc::boxed::Box;
use awkernel_drivers::uart::pl011::PL011;
use awkernel_lib::{
    arch::aarch64::{armv8_timer::Armv8Timer, rpi_system_timer::RpiSystemTimer, set_max_affinity},
    console::{register_console, register_unsafe_puts, unsafe_puts},
    device_tree::{
        prop::{PropertyValue, Range},
        traits::HasNamedChildNode,
    },
    err_msg,
    memory::PAGESIZE,
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
pub static TIMER_RPI: RpiSystemTimer = RpiSystemTimer::new(1, 0x3f003000);

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
            vm.push_device_range(start, end)?;
        }

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

        let _ = vm.remove_heap(0, vm::get_kernel_start() as usize);

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
        self.init_timer()?;
        self.init_gpio()?;
        self.init_i2c()?;

        Ok(())
    }
}

impl Raspi {
    pub const fn new(device_tree: DeviceTreeRef, device_tree_base: usize) -> Self {
        Raspi {
            symbols: None,
            interrupt: None,
            interrupt_compatible: "",
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
            _ => return Err(err_msg!("compatible property has not string value")),
        };

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

        unsafe { unsafe_puts("uart0 has been successfully initialized.\n") };

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

        interrupt_ctl::init_interrupt_controller(self.interrupt_compatible, intc)
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
        let i2c_node = self.get_device_from_symbols("i2c")
            .or(Err(err_msg!("could not find I2C's device node")))?;
        let base_addr = i2c_node
            .get_address(0)
            .or(Err(err_msg!("could not find I2C's base address")))?;
    
        log::info!("I2C: 0x{base_addr:016x}");
    
        unsafe { awkernel_drivers::hal::rpi::i2c::set_i2c_base(base_addr as usize) };
    
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
}
