use awkernel_lib::delay::{wait_microsec, wait_millisec};

use crate::pcie::PCIeInfo;

use super::{
    igc_defines::*,
    igc_hw::{IgcHw, IgcOperations},
    IgcDriverErr,
};

/// In the case of a PHY power down to save power, or to turn off link during a
/// driver unload, or wake on lan is not enabled, restore the link to previous
/// settings.
pub(super) fn igc_power_up_phy_copper(
    ops: &dyn IgcOperations,
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
    ops: &dyn IgcOperations,
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
