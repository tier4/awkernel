use self::{config::UART_IRQ, memory::UART0_BASE, uart::unsafe_puts};
use alloc::boxed::Box;
use awkernel_drivers::uart::pl011::PL011;
use awkernel_lib::{
    console::{register_console, unsafe_print_hex_u128, unsafe_print_hex_u32},
    device_tree::{
        device_tree::DeviceTree,
        error::DeviceTreeError,
        node::{ArrayedNode, DeviceTreeNode},
        print_device_tree_node,
        prop::{NodeProperty, PropertyValue, Range},
        utils::Addr,
    },
    interrupt::register_interrupt_controller,
    local_heap,
};
use core::{arch::asm, ptr::write_volatile};

use super::{DeviceTreeRef, StaticArrayedNode};

pub mod config;
pub mod memory;
mod uart;

type DeviceTreeNodeRef = &'static DeviceTreeNode<'static, local_heap::LocalHeap<'static>>;

static mut SYMBOLS_NODE: Option<super::DeviceTreeNodeRef> = None;
static mut INTERRUPT_NODE: Option<super::DeviceTreeNodeRef> = None;

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
) -> Result<(), DeviceTreeError> {
    let arrayed_node = get_device_from_symbols(device_tree, "uart0")?;

    let base_addr = arrayed_node.get_address()?;

    unsafe {
        unsafe_puts("init_uart0: base_addr = ");
        unsafe_print_hex_u32(base_addr as u32);
        unsafe_puts("\n");
    }

    Ok(())
}

/// Find "__symbols__" node and initialize `ALIASES_NODE` by the node.
fn init_symbols_node(device_tree: super::DeviceTreeRef) -> Option<()> {
    // Find "aliases" node.
    let symbols = device_tree
        .root()
        .nodes()
        .iter()
        .find(|node| node.name() == "__symbols__")?;

    unsafe { write_volatile(&mut SYMBOLS_NODE, Some(symbols)) };

    Some(())
}

/// If `name = "/soc/serial"`,
/// then `Some([Some(root node), Some(soc node), Some(serial node), None, ...])`
/// will be returned.
///
/// If there is no such node, `None` will be returned.
fn get_device_from_symbols(
    device_tree: super::DeviceTreeRef,
    name: &str,
) -> Result<StaticArrayedNode, DeviceTreeError> {
    let symbol_node = unsafe { SYMBOLS_NODE.ok_or(DeviceTreeError::InvalidSemantics)? };
    let alias = symbol_node
        .props()
        .iter()
        .find(|prop| prop.name() == name)
        .ok_or(DeviceTreeError::InvalidSemantics)?;

    let abs_path = match alias.value() {
        PropertyValue::String(p) => *p,
        _ => return Err(DeviceTreeError::InvalidSemantics),
    };

    device_tree.root().get_arrayed_node(abs_path)
}

fn init_interrupt_node(device_tree: super::DeviceTreeRef) -> Result<(), DeviceTreeError> {
    let intc = get_device_from_symbols(device_tree, "gicv2")
        .or(get_device_from_symbols(device_tree, "intc"))?;

    let leaf = intc
        .get_leaf_node()
        .ok_or(DeviceTreeError::InvalidSemantics)?;

    unsafe { write_volatile(&mut INTERRUPT_NODE, Some(leaf)) };

    Ok(())
}

pub(super) struct Raspi;

impl super::SoC for Raspi {
    unsafe fn init_device(device_tree: super::DeviceTreeRef) {
        init_symbols_node(device_tree);
        let _ = init_interrupt_node(device_tree);
        let _ = init_uart0(device_tree);
    }

    unsafe fn init_memory_map(device_tree: super::DeviceTreeRef) {}

    unsafe fn init(device_tree: super::DeviceTreeRef) {}
}
