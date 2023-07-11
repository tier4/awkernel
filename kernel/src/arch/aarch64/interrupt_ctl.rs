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
