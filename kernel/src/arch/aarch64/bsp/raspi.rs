use self::{config::UART_IRQ, memory::UART0_BASE};
use alloc::boxed::Box;
use awkernel_drivers::uart::pl011::PL011;
use awkernel_lib::{
    console::register_console,
    device_tree::{device_tree::DeviceTree, node::DeviceTreeNode, prop::PropertyValue},
    interrupt::register_interrupt_controller,
    local_heap,
};
use core::arch::asm;

use super::DeviceTreeRef;

pub mod config;
pub mod memory;
mod uart;

type DeviceTreeNodeRef = &'static DeviceTreeNode<'static, local_heap::LocalHeap<'static>>;

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

pub unsafe fn init_device() {
    uart::init();
    awkernel_lib::console::register_unsafe_puts(uart::unsafe_puts);
}

fn get_soc_node(device_tree: DeviceTreeRef) -> Option<DeviceTreeNodeRef> {
    device_tree
        .root()
        .nodes()
        .iter()
        .find(|n| n.name() == "soc")
}

fn init_uart0(
    device_tree: &'static DeviceTree<'static, local_heap::LocalHeap<'static>>,
) -> Option<()> {
    // Find "aliases" node.
    let aliases = device_tree
        .root()
        .nodes()
        .iter()
        .find(|node| node.name() == "aliases")?;

    // Find "uart0" property.
    let uart0_alias = aliases.props().iter().find(|prop| prop.name() == "uart0")?;

    // Get the path to "uart0".
    let uart0_path = match uart0_alias.value() {
        PropertyValue::String(p) => *p,
        _ => return None,
    };

    // Split the path by "/".
    let mut path_it = uart0_path.split("/");

    // The root node must be empty.
    let root = path_it.next()?;
    if root != "" {
        return None;
    }

    // The root node must be empty.
    let soc = path_it.next()?;
    if soc != "soc" {
        return None;
    }

    let uart0_name = path_it.next()?;

    let soc_node = get_soc_node(device_tree)?;

    let uart0_node = soc_node.nodes().iter().find(|n| n.name() == uart0_name)?;

    let compatible = uart0_node
        .props()
        .iter()
        .find(|p| p.name() == "compatible")?;

    // UART0 must be PL011.
    match compatible.value() {
        PropertyValue::Strings(comps) => {
            if !comps.contains(&"arm,pl011") {
                return None;
            }
        }
        _ => return None,
    }

    let soc_ranges = match soc_node
        .props()
        .iter()
        .find(|p| p.name() == "ranges")?
        .value()
    {
        PropertyValue::Ranges(ranges) => ranges,
        _ => return None,
    };

    let uart0_addr = match uart0_node
        .props()
        .iter()
        .find(|p| p.name() == "reg")?
        .value()
    {
        PropertyValue::Address(addr, _) => addr,
        _ => return None,
    };

    for range in soc_ranges {
        if let Some(addr) = range.map_to(*uart0_addr) {
            // TODO

            return Some(());
        }
    }

    None
}

struct Raspi;

impl super::SoC for Raspi {
    unsafe fn init_device(device_tree: super::DeviceTreeRef) {}

    unsafe fn init_memory_map(device_tree: super::DeviceTreeRef) {}

    unsafe fn init(device_tree: super::DeviceTreeRef) {}
}
