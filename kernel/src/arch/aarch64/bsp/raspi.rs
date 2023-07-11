use self::{config::UART_IRQ, memory::UART0_BASE, uart::unsafe_puts};
use crate::arch::aarch64::interrupt_ctl;
use alloc::boxed::Box;
use awkernel_drivers::uart::pl011::PL011;
use awkernel_lib::{
    console::register_console,
    device_tree::{device_tree::DeviceTree, prop::PropertyValue},
    interrupt::register_interrupt_controller,
    local_heap,
};
use core::arch::asm;

use super::{DeviceTreeNodeRef, DeviceTreeRef, StaticArrayedNode};

pub mod config;
pub mod memory;
mod uart;

pub fn start_non_primary() {
    if cfg!(feature = "raspi3") {
        unsafe {
            asm!(
                "mov {0}, #0xe0
                 ldr {1}, =_start
                 str {1}, [{0}]     // core #1
                 str {1}, [{0},  8] // core #2
                 str {1}, [{0}, 16] // core #3",
            lateout(reg) _,
            lateout(reg) _
            );
        }
    }
}

#[cfg(feature = "raspi4")]
mod timer {
    use awkernel_lib::arch::aarch64::arm_timer::ArmTimer;
    pub static TIMER: ArmTimer = ArmTimer::new(30);
}

#[cfg(feature = "raspi4")]
pub fn init() {
    init_uart();

    // Set-up the interrupt controller.
    let gic = awkernel_drivers::interrupt_controler::gicv2::GICv2::new(
        memory::GIC_V2_CPU_INTERFACE_BASE,
        memory::GIC_V2_DISTRIBUTOR_BASE,
    );
    register_interrupt_controller(Box::new(gic));

    // Set-up timer.
    awkernel_lib::timer::register_timer(&timer::TIMER);
}

#[cfg(feature = "raspi3")]
mod timer {
    use awkernel_lib::arch::aarch64::rpi_system_timer::RpiSystemTimer;

    use super::memory::MMIO_BASE;
    pub static TIMER: RpiSystemTimer = RpiSystemTimer::new(1, MMIO_BASE + 0x3000);
}

#[cfg(feature = "raspi3")]
pub fn init() {
    init_uart();

    // Set-up the interrupt controller.
    let ctrl = awkernel_drivers::interrupt_controler::bcm2835::BCM2835IntCtrl::new(
        memory::INTERRUPT_CTRL_BASE,
    );
    register_interrupt_controller(Box::new(ctrl));

    // Set-up timer.
    awkernel_lib::timer::register_timer(&timer::TIMER);
}

fn init_uart() {
    let port = Box::new(PL011::new(UART0_BASE, UART_IRQ));
    register_console(port);
}

pub(super) struct Raspi {
    symbols: Option<DeviceTreeNodeRef>,
    interrupt: Option<DeviceTreeNodeRef>,
    interrupt_compatible: &'static str,
}

impl super::SoC for Raspi {
    unsafe fn init_device(&mut self, device_tree: DeviceTreeRef) -> Result<(), &'static str> {
        self.init_symbols(device_tree)
            .ok_or("failed to initialize __symbols__ node")?;
        self.init_interrupt(device_tree)?;
        self.init_uart0(device_tree)?;

        Ok(())
    }

    unsafe fn init_virtual_memory(&self, device_tree: DeviceTreeRef) {}

    unsafe fn init(&self, device_tree: DeviceTreeRef) {}
}

impl Raspi {
    pub const fn new() -> Self {
        Raspi {
            symbols: None,
            interrupt: None,
            interrupt_compatible: "",
        }
    }

    /// Find "__symbols__" node and initialize `ALIASES_NODE` by the node.
    fn init_symbols(&mut self, device_tree: DeviceTreeRef) -> Option<()> {
        // Find "aliases" node.
        let symbols = device_tree.root().get_node("__symbols__")?;

        self.symbols = Some(symbols);

        Some(())
    }

    fn init_interrupt(&mut self, device_tree: DeviceTreeRef) -> Result<(), &'static str> {
        let intc = self
            .get_device_from_symbols(device_tree, "gicv2")
            .or(self.get_device_from_symbols(device_tree, "intc"))
            .or(Err("failed to get the interrupt node"))?;

        let leaf = intc.get_leaf_node().unwrap();

        let compatible_prop = leaf
            .get_property("compatible")
            .ok_or("interrupt node has no compatible property")?;

        self.interrupt_compatible = match compatible_prop.value() {
            PropertyValue::String(s) => s,
            _ => return Err("compatible property has not string value"),
        };

        self.interrupt = Some(leaf);

        Ok(())
    }

    /// If `name = "/soc/serial"`,
    /// then `Some([Some(root node), Some(soc node), Some(serial node), None, ...])`
    /// will be returned.
    ///
    /// If there is no such node, `None` will be returned.
    fn get_device_from_symbols(
        &self,
        device_tree: DeviceTreeRef,
        name: &str,
    ) -> Result<StaticArrayedNode, &'static str> {
        let Some(symbols) = self.symbols.as_ref() else {
            return Err("the symbols node has not been initialized");
        };

        let alias = symbols
            .get_property(name)
            .ok_or("could not find such property")?;

        let abs_path = match alias.value() {
            PropertyValue::String(p) => *p,
            _ => return Err("__symbols__ is not a string"),
        };

        device_tree
            .root()
            .get_arrayed_node(abs_path)
            .or(Err("invalid path"))
    }

    fn init_uart0(
        &self,
        device_tree: &'static DeviceTree<'static, local_heap::LocalHeap<'static>>,
    ) -> Result<(), &'static str> {
        let arrayed_node = self
            .get_device_from_symbols(device_tree, "uart0")
            .or(Err("could not find uart0"))?;

        // Get the base address.
        let base_addr = arrayed_node
            .get_address()
            .or(Err("failed to calculate uart0's base address"))?;

        let uart0_node = arrayed_node.get_leaf_node().unwrap();

        // Get the compatible property.
        let compatible_prop = uart0_node
            .get_property("compatible")
            .ok_or("uart0 has no compatible property")?;

        let compatibles = match compatible_prop.value() {
            PropertyValue::Strings(v) => v,
            _ => return Err("uart0's compatible property is not a string vector"),
        };

        // UART0 must be PL011.
        compatibles
            .iter()
            .find(|c| **c == "arm,pl011")
            .ok_or("UART0 is not PL011")?;

        let interrupts_prop = uart0_node
            .get_property("interrupts")
            .ok_or("uart0 has no interrupt property")?;

        let interrupts = match interrupts_prop.value() {
            PropertyValue::Integers(ints) => ints,
            _ => return Err("uart0's compatible property is not a integer vector"),
        };

        let irq = interrupt_ctl::get_irq(self.interrupt_compatible, interrupts)
            .ok_or("failed to get UART0's IRQ#")?;

        uart::init(base_addr as usize, irq);

        unsafe { unsafe_puts("uart0 has been successfully initialized.\n") };

        Ok(())
    }
}
