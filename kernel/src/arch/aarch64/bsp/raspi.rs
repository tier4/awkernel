use self::{config::UART_IRQ, memory::UART0_BASE, uart::unsafe_puts};
use alloc::boxed::Box;
use awkernel_drivers::uart::pl011::PL011;
use awkernel_lib::{
    console::{register_console, unsafe_print_hex_u128, unsafe_print_hex_u32},
    device_tree::{
        device_tree::DeviceTree,
        node::DeviceTreeNode,
        print_device_tree_node,
        prop::{NodeProperty, PropertyValue, Range},
        utils::Addr,
    },
    interrupt::register_interrupt_controller,
    local_heap,
};
use core::{arch::asm, ptr::write_volatile};

use super::DeviceTreeRef;

pub mod config;
pub mod memory;
mod uart;

type DeviceTreeNodeRef = &'static DeviceTreeNode<'static, local_heap::LocalHeap<'static>>;

static mut ALIASES_NODE: Option<super::DeviceTreeNoeRef> = None;
static mut INTERRUPT_NODE: Option<super::DeviceTreeNoeRef> = None;

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
    let nodes = get_device_from_aliases(device_tree, "uart0")?;

    let mut uart0_node = None;
    let mut base_addr = 0;
    'node: for node in nodes.iter().rev() {
        if node.is_some() {
            // Find UART0 node and its base address.
            if uart0_node.is_none() {
                let uart0 = node.unwrap();
                let reg = uart0.props().iter().find(|prop| prop.name() == "reg")?;

                match reg.value() {
                    PropertyValue::Address(base, _len) => {
                        base_addr = base.to_u128();
                    }
                    _ => return None,
                }

                uart0_node = Some(uart0);
            } else {
                let n = node.unwrap();
                if let Some(ranges) = n.props().iter().find(|p| p.name() == "ranges") {
                    match ranges.value() {
                        PropertyValue::Ranges(rgs) => {
                            // `base_addr` must be in the ranges,
                            // and it will be mapped by the ranges.
                            for range in rgs {
                                if let Some(addr) = range.map_to(Addr::U128(base_addr)) {
                                    base_addr = addr;
                                    continue 'node;
                                }
                            }
                            return None; // Invalid address.
                        }
                        _ => return None, // Must be ranges.
                    }
                }
            }
        }
    }

    unsafe {
        unsafe_puts("init_uart0: base_addr = ");
        unsafe_print_hex_u32(base_addr as u32);
        unsafe_puts("\n");
    }

    Some(())
}

/// Find "aliases" node and initialize `ALIASES_NODE` by the node.
fn init_alias_node(device_tree: super::DeviceTreeRef) -> Option<()> {
    // Find "aliases" node.
    let aliases = device_tree
        .root()
        .nodes()
        .iter()
        .find(|node| node.name() == "aliases")?;

    unsafe { write_volatile(&mut ALIASES_NODE, Some(aliases)) };

    Some(())
}

/// If `name = "/soc/serial"`,
/// then `Some([Some(root node), Some(soc node), Some(serial node), None, ...])`
/// will be returned.
///
/// If there is no such node, `None` will be returned.
fn get_device_from_aliases(
    device_tree: super::DeviceTreeRef,
    name: &str,
) -> Option<[Option<DeviceTreeNodeRef>; 10]> {
    let aliases = unsafe { ALIASES_NODE? };
    let alias = aliases.props().iter().find(|prop| prop.name() == name)?;

    let abs_path = match alias.value() {
        PropertyValue::String(p) => *p,
        _ => return None,
    };

    let mut node = device_tree.root();
    let mut result = [None; 10];

    let mut path_it = abs_path.split("/");
    let first = path_it.next()?;

    if first != "" {
        return None;
    }

    result[0] = Some(node);

    for (i, p) in path_it.enumerate() {
        node = node.nodes().iter().find(|n| n.name() == p)?;
        result[i + 1] = Some(node);
    }

    Some(result)
}

pub(super) struct Raspi;

impl super::SoC for Raspi {
    unsafe fn init_device(device_tree: super::DeviceTreeRef) {
        init_alias_node(device_tree);
        init_uart0(device_tree);
    }

    unsafe fn init_memory_map(device_tree: super::DeviceTreeRef) {}

    unsafe fn init(device_tree: super::DeviceTreeRef) {}
}
