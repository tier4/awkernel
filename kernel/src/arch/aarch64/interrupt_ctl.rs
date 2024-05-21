use super::bsp::StaticArrayedNode;
use alloc::boxed::Box;
use awkernel_lib::{err_msg, interrupt::register_interrupt_controller};

#[allow(dead_code)]
pub fn get_irq(irc_ctl: &str, interrupts: &[u64]) -> Option<u16> {
    match irc_ctl {
        "brcm,bcm2836-armctrl-ic" => get_irq_bcm2836(interrupts),
        "arm,gic-400" | "arm,gic-v3" => get_irq_gicv2(interrupts),
        _ => None,
    }
}

#[allow(dead_code)]
fn get_irq_bcm2836(interrupts: &[u64]) -> Option<u16> {
    let int0 = interrupts.first()?;
    let int1 = interrupts.get(1)?;

    match int0 {
        0 => Some(*int1 as u16),      // IRQ Basic
        1 => Some(*int1 as u16),      // IRQ 1
        2 => Some(*int1 as u16 + 32), // IRQ 2
        _ => None,
    }
}

#[allow(dead_code)]
fn get_irq_gicv2(interrupts: &[u64]) -> Option<u16> {
    let int0 = interrupts.first()?;
    let int1 = interrupts.get(1)?;

    match int0 {
        0 => Some(*int1 as u16 + 32), // SPI
        1 => Some(*int1 as u16),      // PPI
        _ => None,
    }
}

#[allow(dead_code)]
fn init_gicv2(node: &StaticArrayedNode) -> Result<(), &'static str> {
    let gicd_base = node
        .get_address(0)
        .or(Err(err_msg!("could not find GICD_BASE")))? as usize;
    let gicc_base = node
        .get_address(1)
        .or(Err(err_msg!("could not find GICC_BASE")))? as usize;

    let gic = awkernel_drivers::interrupt_controller::gicv2::GICv2::new(gicd_base, gicc_base);

    register_interrupt_controller(Box::new(gic));

    log::info!("GICv2 has been initialized.");
    log::info!("GICD_BASE = 0x{gicd_base:016x}");
    log::info!("GICC_BASE = 0x{gicc_base:016x}");

    Ok(())
}

#[allow(dead_code)]
fn init_gicv3(node: &StaticArrayedNode) -> Result<(), &'static str> {
    let gicd_base = node
        .get_address(0)
        .or(Err(err_msg!("could not find GICD_BASE")))? as usize;
    let gicr_base = node
        .get_address(1)
        .or(Err(err_msg!("could not find GICR_BASE")))? as usize;

    let mut its_base = None;
    if let Some(leaf) = node.get_leaf_node() {
        for its_node in leaf.nodes().iter() {
            if its_node.name().starts_with("its@") {
                if !its_node.compatible(&["arm,gic-v3-its"]) {
                    continue;
                }

                let mut arr_its_node = node.clone();
                arr_its_node
                    .push(its_node)
                    .or(Err(err_msg!("could not push the ITS node")))?;

                match arr_its_node.get_address(0) {
                    Ok(addr) => its_base = Some(addr as usize),
                    Err(e) => log::error!("{e:?}: ITS node has no address"),
                }

                break;
            }
        }
    }

    let gic =
        awkernel_drivers::interrupt_controller::gicv3::GICv3::new(gicd_base, gicr_base, its_base);

    register_interrupt_controller(Box::new(gic));

    log::info!("GICv3 has been initialized.");
    log::info!("GICD_BASE = 0x{gicd_base:016x}");
    log::info!("GICR_BASE = 0x{gicr_base:016x}");

    if let Some(its_base) = its_base {
        log::info!("ITS_BASE  = 0x{its_base:016x}");
    }

    Ok(())
}

#[allow(dead_code)]
fn init_bcm2836(
    node: &StaticArrayedNode,
    local_intc_node: &StaticArrayedNode,
) -> Result<(), &'static str> {
    let base = node.get_address(0).or(Err(err_msg!(
        "could not find the base address for global interrupts"
    )))? as usize;

    let local_base = local_intc_node.get_address(0).or(Err(err_msg!(
        "could not find the base address for local interrupts"
    )))? as usize;

    let ctrl =
        awkernel_drivers::interrupt_controller::bcm2835::BCM2835IntCtrl::new(base, local_base);
    register_interrupt_controller(Box::new(ctrl));

    log::info!("bcm2836-armctrl-ic has been initialized.");
    log::info!("bcm2836-armctrl-ic: 0x{base:016x}");
    log::info!("bcm2836-l1-intc: 0x{local_base:016x}");

    Ok(())
}

#[allow(dead_code)]
pub fn init_interrupt_controller(
    irc_ctl: &str,
    intc_node: &StaticArrayedNode,
    local_irc_ctl: Option<&str>,
    local_intc_node: Option<&StaticArrayedNode>,
) -> Result<(), &'static str> {
    match irc_ctl {
        "brcm,bcm2836-armctrl-ic" => {
            if let Some("brcm,bcm2836-l1-intc") = local_irc_ctl {
                let local_intc_node = local_intc_node
                    .as_ref()
                    .ok_or(err_msg!("local_intc_node is None"))?;
                init_bcm2836(intc_node, local_intc_node)
            } else {
                Err("")
            }
        }
        "arm,gic-400" => init_gicv2(intc_node),
        "arm,gic-v3" => init_gicv3(intc_node),
        _ => Err(err_msg!("unsupported interrupt controller")),
    }
}
