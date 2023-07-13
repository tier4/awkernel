use alloc::boxed::Box;
use awkernel_lib::{err_msg, interrupt::register_interrupt_controller};

use super::bsp::StaticArrayedNode;

pub fn get_irq(irc_ctl: &str, interrupts: &[u64]) -> Option<u16> {
    match irc_ctl {
        "brcm,bcm2836-armctrl-ic" => get_irq_bcm2836(interrupts),
        "arm,gic-400" => get_irq_gicv2(interrupts),
        _ => None,
    }
}

fn get_irq_bcm2836(interrupts: &[u64]) -> Option<u16> {
    let int0 = interrupts.get(0)?;
    let int1 = interrupts.get(1)?;

    match int0 {
        0 => Some(*int1 as u16),      // IRQ Basic
        1 => Some(*int1 as u16),      // IRQ 1
        2 => Some(*int1 as u16 + 32), // IRQ 2
        _ => None,
    }
}

fn get_irq_gicv2(interrupts: &[u64]) -> Option<u16> {
    let int0 = interrupts.get(0)?;
    let int1 = interrupts.get(1)?;

    match int0 {
        0 => Some(*int1 as u16 + 32), // SPI
        1 => Some(*int1 as u16),      // PPI
        _ => None,
    }
}

fn init_gicv2(node: &StaticArrayedNode) -> Result<(), &'static str> {
    let gicd_base = node
        .get_address(0)
        .or(Err(err_msg!("could not find GICD_BASE")))? as usize;
    let gicc_base = node
        .get_address(1)
        .or(Err(err_msg!("could not find GICC_BASE")))? as usize;

    let gic = awkernel_drivers::interrupt_controler::gicv2::GICv2::new(gicd_base, gicc_base);
    register_interrupt_controller(Box::new(gic));

    log::info!("GICv2 has been initialized.");
    log::info!("GICD_BASE = 0x{gicd_base:016x}");
    log::info!("GICC_BASE = 0x{gicc_base:016x}");

    Ok(())
}

fn init_bcm2836(node: &StaticArrayedNode) -> Result<(), &'static str> {
    let base = node
        .get_address(0)
        .or(Err(err_msg!("could not find the base address")))? as usize;

    let ctrl = awkernel_drivers::interrupt_controler::bcm2835::BCM2835IntCtrl::new(base);
    register_interrupt_controller(Box::new(ctrl));

    log::info!("bcm2836-armctrl-ic has been initialized.");
    log::info!("bcm2836-armctrl-ic: base = 0x{base:016x}");

    Ok(())
}

pub fn init_interrupt_controller(
    irc_ctl: &str,
    intc_node: &StaticArrayedNode,
) -> Result<(), &'static str> {
    match irc_ctl {
        "brcm,bcm2836-armctrl-ic" => init_bcm2836(intc_node),
        "arm,gic-400" => init_gicv2(intc_node),
        _ => Err(err_msg!("unsupported interrupt controller")),
    }
}
