use awkernel_lib::delay::{wait_microsec, wait_millisec};

use crate::pcie::{intel::igc::IgcFcMode, PCIeInfo};

use super::{
    igc_defines::*,
    igc_hw::{IgcHw, IgcPhyOperations},
    igc_regs::*,
    read_reg, write_flush, write_reg, IgcDriverErr,
};

// IGP01IGC Specific Registers
const IGP01IGC_PHY_PORT_CONFIG: u32 = 0x10; // Port Config
const IGP01IGC_PHY_PORT_STATUS: u32 = 0x11; // Status
const IGP01IGC_PHY_PORT_CTRL: u32 = 0x12; // Control
const IGP01IGC_PHY_LINK_HEALTH: u32 = 0x13; // PHY Link Health
const IGP02IGC_PHY_POWER_MGMT: u32 = 0x19; // Power Management
const IGP01IGC_PHY_PAGE_SELECT: u32 = 0x1F; // Page Select
const BM_PHY_PAGE_SELECT: u32 = 22; // Page Select for BM
const IGP_PAGE_SHIFT: u32 = 5;
const PHY_REG_MASK: u32 = 0x1F;
const IGC_I225_PHPM: usize = 0x0E14; // I225 PHY Power Management
const IGC_I225_PHPM_DIS_1000_D3: u32 = 0x0008; // Disable 1G in D3
const IGC_I225_PHPM_LINK_ENERGY: u32 = 0x0010; // Link Energy Detect
const IGC_I225_PHPM_GO_LINKD: u32 = 0x0020; // Go Link Disconnect
const IGC_I225_PHPM_DIS_1000: u32 = 0x0040; // Disable 1G globally
const IGC_I225_PHPM_SPD_B2B_EN: u32 = 0x0080; // Smart Power Down Back2Back
const IGC_I225_PHPM_RST_COMPL: u32 = 0x0100; // PHY Reset Completed
const IGC_I225_PHPM_DIS_100_D3: u32 = 0x0200; // Disable 100M in D3
const IGC_I225_PHPM_ULP: u32 = 0x0400; // Ultra Low-Power Mode
const IGC_I225_PHPM_DIS_2500: u32 = 0x0800; // Disable 2.5G globally
const IGC_I225_PHPM_DIS_2500_D3: u32 = 0x1000; // Disable 2.5G in D3

/// Reads the MDI control register in the PHY at offset and stores the
/// information read to data.
fn igc_read_phy_reg_mdic(
    info: &mut PCIeInfo,
    hw: &IgcHw,
    offset: u32,
) -> Result<u16, IgcDriverErr> {
    if offset > MAX_PHY_REG_ADDRESS {
        return Err(IgcDriverErr::Param);
    }

    // Set up Op-code, Phy Address, and register offset in the MDI
    // Control register.  The MAC will take care of interfacing with the
    // PHY to retrieve the desired data.
    let mut mdic =
        (offset << IGC_MDIC_REG_SHIFT) | (hw.phy.addr << IGC_MDIC_PHY_SHIFT) | IGC_MDIC_OP_READ;

    write_reg(info, IGC_MDIC, mdic)?;

    // Poll the ready bit to see if the MDI read completed
    // Increasing the time out as testing showed failures with
    // the lower time out
    for _ in 0..(IGC_GEN_POLL_TIMEOUT * 3) {
        wait_microsec(50);
        mdic = read_reg(info, IGC_MDIC)?;
        if mdic & IGC_MDIC_READY != 0 {
            break;
        }
    }

    if mdic & IGC_MDIC_READY == 0 {
        return Err(IgcDriverErr::Phy);
    }
    if mdic & IGC_MDIC_ERROR != 0 {
        return Err(IgcDriverErr::Phy);
    }
    if (mdic & IGC_MDIC_REG_MASK) >> IGC_MDIC_REG_SHIFT != offset {
        return Err(IgcDriverErr::Phy);
    }

    Ok(mdic as u16)
}

/// Writes data to MDI control register in the PHY at offset.
fn igc_write_phy_reg_mdic(
    info: &mut PCIeInfo,
    hw: &IgcHw,
    offset: u32,
    data: u16,
) -> Result<(), IgcDriverErr> {
    if offset > MAX_PHY_REG_ADDRESS {
        return Err(IgcDriverErr::Param);
    }

    // Set up Op-code, Phy Address, and register offset in the MDI
    // Control register.  The MAC will take care of interfacing with the
    // PHY to retrieve the desired data.
    let mut mdic = (data as u32)
        | (offset << IGC_MDIC_REG_SHIFT)
        | (hw.phy.addr << IGC_MDIC_PHY_SHIFT)
        | IGC_MDIC_OP_WRITE;

    write_reg(info, IGC_MDIC, mdic)?;

    // Poll the ready bit to see if the MDI read completed
    // Increasing the time out as testing showed failures with
    // the lower time out
    for _ in 0..(IGC_GEN_POLL_TIMEOUT * 3) {
        wait_microsec(50);
        mdic = read_reg(info, IGC_MDIC)?;
        if mdic & IGC_MDIC_READY != 0 {
            break;
        }
    }

    if mdic & IGC_MDIC_READY == 0 {
        return Err(IgcDriverErr::Phy);
    }
    if mdic & IGC_MDIC_ERROR != 0 {
        return Err(IgcDriverErr::Phy);
    }
    if (mdic & IGC_MDIC_REG_MASK) >> IGC_MDIC_REG_SHIFT != offset {
        return Err(IgcDriverErr::Phy);
    }

    Ok(())
}

fn igc_access_xmdio_reg(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    address: u16,
    dev_addr: u8,
    data: &mut u16,
    read: bool,
) -> Result<(), IgcDriverErr> {
    ops.write_reg(info, hw, IGC_MMDAC, dev_addr as u16)?;
    ops.write_reg(info, hw, IGC_MMDAAD, address)?;
    ops.write_reg(info, hw, IGC_MMDAC, IGC_MMDAC_FUNC_DATA | dev_addr as u16)?;

    if read {
        *data = ops.read_reg(info, hw, IGC_MMDAAD)?;
    } else {
        ops.write_reg(info, hw, IGC_MMDAAD, *data)?;
    };

    // Recalibrate the device back to 0
    ops.write_reg(info, hw, IGC_MMDAC, 0)
}

fn igc_read_xmdio_reg(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    address: u16,
    dev_addr: u8,
) -> Result<u16, IgcDriverErr> {
    let mut data = 0;
    igc_access_xmdio_reg(ops, info, hw, address, dev_addr, &mut data, true)?;
    Ok(data)
}

fn igc_write_xmdio_reg(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    address: u16,
    dev_addr: u8,
    mut data: u16,
) -> Result<u16, IgcDriverErr> {
    igc_access_xmdio_reg(ops, info, hw, address, dev_addr, &mut data, false)?;
    Ok(data)
}

/// Acquires semaphore, if necessary, then writes the data to PHY register
/// at the offset.  Release any acquired semaphores before exiting.
pub(super) fn igc_write_phy_reg_gpy(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    offset: u32,
    data: u16,
) -> Result<(), IgcDriverErr> {
    let dev_addr = (offset & GPY_MMD_MASK) >> GPY_MMD_SHIFT;
    let offset = offset & GPY_REG_MASK;

    if dev_addr == 0 {
        acquire_phy(ops, info, hw, |_, info, hw| {
            igc_write_phy_reg_mdic(info, hw, offset, data)
        })
    } else {
        igc_write_xmdio_reg(ops, info, hw, offset as u16, dev_addr as u8, data)?;
        Ok(())
    }
}

pub(super) fn igc_read_phy_reg_gpy(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    offset: u32,
) -> Result<u16, IgcDriverErr> {
    let dev_addr = (offset & GPY_MMD_MASK) >> GPY_MMD_SHIFT;
    let offset = offset & GPY_REG_MASK;

    if dev_addr == 0 {
        acquire_phy(ops, info, hw, |_, info, hw| {
            igc_read_phy_reg_mdic(info, hw, offset)
        })
    } else {
        igc_read_xmdio_reg(ops, info, hw, offset as u16, dev_addr as u8)
    }
}

/// In the case of a PHY power down to save power, or to turn off link during a
/// driver unload, or wake on lan is not enabled, restore the link to previous
/// settings.
pub(super) fn igc_power_up_phy_copper(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    // The PHY will retain its settings across a power down/up cycle
    let mut mii_reg = ops.read_reg(info, hw, PHY_CONTROL)?;
    mii_reg &= !MII_CR_POWER_DOWN;
    ops.write_reg(info, hw, PHY_CONTROL, mii_reg)?;
    wait_microsec(300);

    Ok(())
}

/// In the case of a PHY power down to save power, or to turn off link during a
/// driver unload, or wake on lan is not enabled, restore the link to previous
/// settings.
pub(super) fn igc_power_down_phy_copper(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    // The PHY will retain its settings across a power down/up cycle
    let mut mii_reg = ops.read_reg(info, hw, PHY_CONTROL)?;
    mii_reg |= MII_CR_POWER_DOWN;
    ops.write_reg(info, hw, PHY_CONTROL, mii_reg)?;
    wait_millisec(1);

    Ok(())
}

fn acquire_phy<F, R>(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    f: F,
) -> Result<R, IgcDriverErr>
where
    F: Fn(&dyn IgcPhyOperations, &mut PCIeInfo, &IgcHw) -> Result<R, IgcDriverErr>,
{
    IgcPhyOperations::acquire(ops, info, hw)?;
    let result = f(ops, info, hw);
    IgcPhyOperations::release(ops, info, hw)?;
    result
}

/// Verify the reset block is not blocking us from resetting.  Acquire
/// semaphore (if necessary) and read/set/write the device control reset
/// bit in the PHY.  Wait the appropriate delay time for the device to
/// reset and release the semaphore (if necessary).
pub(super) fn igc_phy_hw_reset_generic(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    match ops.check_reset_block(info) {
        Err(IgcDriverErr::BlkPhyReset) => {
            return Ok(());
        }
        Err(e) => {
            return Err(e);
        }
        _ => (),
    }

    acquire_phy(ops, info, hw, |_, info, hw| {
        let _phpm = read_reg(info, IGC_I225_PHPM)?;

        let ctrl = read_reg(info, IGC_CTRL)?;
        write_reg(info, IGC_CTRL, ctrl | IGC_CTRL_PHY_RST)?;
        write_flush(info)?;

        wait_microsec(hw.phy.reset_delay_us as u64);

        write_reg(info, IGC_CTRL, ctrl)?;
        write_flush(info)?;

        wait_microsec(150);

        for _ in 0..10000 {
            let phpm = read_reg(info, IGC_I225_PHPM)?;
            wait_microsec(1);
            if phpm & IGC_I225_PHPM_RST_COMPL != 0 {
                return Ok(());
            }
        }

        log::debug!("Timeout expired after a phy reset");

        Ok(())
    })
}

/// Reads the PHY registers and stores the PHY ID and possibly the PHY
/// revision in the hardware structure.
pub(super) fn igc_get_phy_id(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    let phy_id = ops.read_reg(info, hw, PHY_ID1)?;

    hw.phy.id = (phy_id as u32) << 16;
    wait_microsec(200);
    let phy_id = ops.read_reg(info, hw, PHY_ID2)?;

    hw.phy.id |= (phy_id as u32) & PHY_REVISION_MASK;
    hw.phy.revision = (phy_id as u32) & !PHY_REVISION_MASK;

    Ok(())
}

pub(super) fn igc_phy_has_link_generic(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    iterations: u32,
    usec_interval: u32,
) -> Result<bool, IgcDriverErr> {
    let mut i = 0;

    for _ in 0..iterations {
        // Some PHYs require the PHY_STATUS register to be read
        // twice due to the link bit being sticky.  No harm doing
        // it across the board.
        if ops.read_reg(info, hw, PHY_STATUS).is_err() {
            // If the first read fails, another entity may have
            // ownership of the resources, wait and try again to
            // see if they have relinquished the resources yet.
            wait_microsec(usec_interval as u64);
        };

        let phy_status = ops.read_reg(info, hw, PHY_STATUS)?;

        if phy_status & MII_SR_LINK_STATUS != 0 {
            break;
        }

        wait_microsec(usec_interval as u64);

        i += 1;
    }

    Ok(i < iterations)
}

/// igc_check_downshift_generic - Checks whether a downshift in speed occurred
/// @hw: pointer to the HW structure
///
/// Success returns 0, Failure returns 1
///
/// A downshift is detected by querying the PHY link health.
pub(super) fn igc_check_downshift_generic(hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
    hw.phy.speed_downgraded = false;
    Ok(())
}

/// Reads the MII auto-neg advertisement register and/or the 1000T control
/// register and if the PHY is already setup for auto-negotiation, then
/// return successful.  Otherwise, setup advertisement and flow control to
/// the appropriate values for the wanted auto-negotiation.
fn igc_phy_setup_autoneg(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    let mut mii_1000t_ctrl_reg = 0;
    let mut aneg_multigbt_an_ctrl = 0;

    hw.phy.autoneg_advertised &= hw.phy.autoneg_mask;

    // Read the MII Auto-Neg Advertisement Register (Address 4).
    let mut mii_autoneg_adv_reg = ops.read_reg(info, hw, PHY_AUTONEG_ADV)?;

    if hw.phy.autoneg_mask & ADVERTISE_1000_FULL != 0 {
        // Read the MII 1000Base-T Control Register (Address 9).
        mii_1000t_ctrl_reg = ops.read_reg(info, hw, PHY_1000T_CTRL)?;
    }

    if hw.phy.autoneg_mask & ADVERTISE_2500_FULL != 0 {
        // Read the MULTI GBT AN Control Register - reg 7.32
        aneg_multigbt_an_ctrl = ops.read_reg(
            info,
            hw,
            (STANDARD_AN_REG_MASK << MMD_DEVADDR_SHIFT) | ANEG_MULTIGBT_AN_CTRL,
        )?;
    }

    // Need to parse both autoneg_advertised and fc and set up
    // the appropriate PHY registers.  First we will parse for
    // autoneg_advertised software override.  Since we can advertise
    // a plethora of combinations, we need to check each bit
    // individually.
    mii_autoneg_adv_reg &= !(NWAY_AR_100TX_FD_CAPS
        | NWAY_AR_100TX_HD_CAPS
        | NWAY_AR_10T_FD_CAPS
        | NWAY_AR_10T_HD_CAPS);
    mii_1000t_ctrl_reg &= !(CR_1000T_HD_CAPS | CR_1000T_FD_CAPS);

    // Do we want to advertise 10 Mb Half Duplex?
    if hw.phy.autoneg_advertised & ADVERTISE_10_HALF != 0 {
        mii_autoneg_adv_reg |= NWAY_AR_10T_HD_CAPS;
    }

    // Do we want to advertise 10 Mb Full Duplex?
    if hw.phy.autoneg_advertised & ADVERTISE_10_FULL != 0 {
        mii_autoneg_adv_reg |= NWAY_AR_10T_FD_CAPS;
    }

    // Do we want to advertise 100 Mb Half Duplex?
    if hw.phy.autoneg_advertised & ADVERTISE_100_HALF != 0 {
        mii_autoneg_adv_reg |= NWAY_AR_100TX_HD_CAPS;
    }

    // Do we want to advertise 100 Mb Full Duplex?
    if hw.phy.autoneg_advertised & ADVERTISE_100_FULL != 0 {
        mii_autoneg_adv_reg |= NWAY_AR_100TX_FD_CAPS;
    }

    // We do not allow the Phy to advertise 1000 Mb Half Duplex
    if hw.phy.autoneg_advertised & ADVERTISE_1000_HALF != 0 {
        log::debug!("Advertise 1000mb Half duplex request denied!");
    }

    // Do we want to advertise 1000 Mb Full Duplex?
    if hw.phy.autoneg_advertised & ADVERTISE_1000_FULL != 0 {
        mii_1000t_ctrl_reg |= CR_1000T_FD_CAPS;
    }

    // We do not allow the Phy to advertise 2500 Mb Half Duplex
    if hw.phy.autoneg_advertised & ADVERTISE_2500_HALF != 0 {
        log::debug!("Advertise 2500mb Half duplex request denied!");
    }

    // Do we want to advertise 2500 Mb Full Duplex?
    if hw.phy.autoneg_advertised & ADVERTISE_2500_FULL != 0 {
        aneg_multigbt_an_ctrl |= CR_2500T_FD_CAPS;
    } else {
        aneg_multigbt_an_ctrl &= !CR_2500T_FD_CAPS;
    }

    // Check for a software override of the flow control settings, and
    // setup the PHY advertisement registers accordingly.  If
    // auto-negotiation is enabled, then software will have to set the
    // "PAUSE" bits to the correct value in the Auto-Negotiation
    // Advertisement Register (PHY_AUTONEG_ADV) and re-start auto-
    // negotiation.
    //
    // The possible values of the "fc" parameter are:
    //      0:  Flow control is completely disabled
    //      1:  Rx flow control is enabled (we can receive pause frames
    //          but not send pause frames).
    //      2:  Tx flow control is enabled (we can send pause frames
    //          but we do not support receiving pause frames).
    //      3:  Both Rx and Tx flow control (symmetric) are enabled.
    //  other:  No software override.  The flow control configuration
    //          in the EEPROM is used.
    match hw.fc.current_mode {
        IgcFcMode::None => {
            // Flow control (Rx & Tx) is completely disabled by a
            // software over-ride.
            mii_autoneg_adv_reg &= !(NWAY_AR_ASM_DIR | NWAY_AR_PAUSE);
        }
        IgcFcMode::RxPause => {
            // Rx Flow control is enabled, and Tx Flow control is
            // disabled, by a software over-ride.
            //
            // Since there really isn't a way to advertise that we are
            // capable of Rx Pause ONLY, we will advertise that we
            // support both symmetric and asymmetric Rx PAUSE.  Later
            // (in igc_config_fc_after_link_up) we will disable the
            // hw's ability to send PAUSE frames.
            mii_autoneg_adv_reg |= NWAY_AR_ASM_DIR | NWAY_AR_PAUSE;
        }
        IgcFcMode::TxPause => {
            // Tx Flow control is enabled, and Rx Flow control is
            // disabled, by a software over-ride.
            mii_autoneg_adv_reg |= NWAY_AR_ASM_DIR;
            mii_autoneg_adv_reg &= !NWAY_AR_PAUSE;
        }
        IgcFcMode::Full => {
            // Flow control (both Rx and Tx) is enabled by a software
            // over-ride.
            mii_autoneg_adv_reg |= NWAY_AR_ASM_DIR | NWAY_AR_PAUSE;
        }
        _ => {
            log::debug!("Flow control param set incorrectly");
            return Err(IgcDriverErr::Config);
        }
    }

    ops.write_reg(info, hw, PHY_AUTONEG_ADV, mii_autoneg_adv_reg)?;

    if hw.phy.autoneg_mask & ADVERTISE_1000_FULL != 0 {
        ops.write_reg(info, hw, PHY_1000T_CTRL, mii_1000t_ctrl_reg)?;
    }

    if hw.phy.autoneg_mask & ADVERTISE_2500_FULL != 0 {
        ops.write_reg(
            info,
            hw,
            (STANDARD_AN_REG_MASK << MMD_DEVADDR_SHIFT) | ANEG_MULTIGBT_AN_CTRL,
            aneg_multigbt_an_ctrl,
        )?;
    }

    Ok(())
}

/// Performs initial bounds checking on autoneg advertisement parameter, then
/// configure to advertise the full capability.  Setup the PHY to autoneg
/// and restart the negotiation process between the link partner.  If
/// autoneg_wait_to_complete, then wait for autoneg to complete before exiting.
fn igc_copper_link_autoneg(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    // Perform some bounds checking on the autoneg advertisement parameter.
    hw.phy.autoneg_advertised &= hw.phy.autoneg_mask;

    // If autoneg_advertised is zero, we assume it was not defaulted
    // by the calling code so we set to advertise full capability.
    if hw.phy.autoneg_advertised == 0 {
        hw.phy.autoneg_advertised = hw.phy.autoneg_mask;
    }

    igc_phy_setup_autoneg(ops, info, hw)?;

    // Restart auto-negotiation by setting the Auto Neg Enable bit and
    // the Auto Neg Restart bit in the PHY control register.
    let mut phy_ctrl = ops.read_reg(info, hw, PHY_CONTROL)?;
    phy_ctrl |= MII_CR_AUTO_NEG_EN | MII_CR_RESTART_AUTO_NEG;
    ops.write_reg(info, hw, PHY_CONTROL, phy_ctrl)?;

    // Does the user want to wait for Auto-Neg to complete here, or
    // check at a later time (for example, callback routine).
    if hw.phy.autoneg_wait_to_complete {
        igc_wait_autoneg(ops, info, hw)?;
    }

    hw.mac.get_link_status = true;

    Ok(())
}

/// Waits for auto-negotiation to complete or for the auto-negotiation time
/// limit to expire, which ever happens first.
fn igc_wait_autoneg(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    // Break after autoneg completes or PHY_AUTO_NEG_LIMIT expires.
    for _ in 0..PHY_AUTO_NEG_LIMIT {
        ops.read_reg(info, hw, PHY_STATUS)?;
        let phy_status = ops.read_reg(info, hw, PHY_STATUS)?;

        if phy_status & MII_SR_AUTONEG_COMPLETE != 0 {
            return Ok(());
        }

        wait_millisec(100);
    }
    // PHY_AUTO_NEG_TIME expiration doesn't guarantee auto-negotiation
    // has completed.
    Ok(())
}
