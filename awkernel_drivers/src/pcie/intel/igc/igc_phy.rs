use awkernel_lib::delay::{wait_microsec, wait_millisec};

use crate::pcie::PCIeInfo;

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
