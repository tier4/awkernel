use crate::pcie::PCIeInfo;

use super::{
    igc_defines::{IGC_SWFW_PHY0_SM, IGC_SWFW_PHY1_SM},
    igc_hw::{IgcHw, IgcOperations, IGC_FUNC_1},
    igc_phy::igc_power_down_phy_copper,
    IgcDriverErr,
};

pub(super) const IGC_RAR_ENTRIES_BASE: u16 = 16;

/// Acquire access rights to the correct PHY.
pub(super) fn igc_acquire_phy_base(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    let mask = if hw.bus.func == IGC_FUNC_1 {
        IGC_SWFW_PHY1_SM
    } else {
        IGC_SWFW_PHY0_SM
    };
    ops.acquire_swfw_sync(info, hw, mask)
}

/// A wrapper to release access rights to the correct PHY.
pub(super) fn igc_release_phy_base(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    let mask = if hw.bus.func == IGC_FUNC_1 {
        IGC_SWFW_PHY1_SM
    } else {
        IGC_SWFW_PHY0_SM
    };

    ops.release_swfw_sync(info, hw, mask)
}

/// In the case of a PHY power down to save power, or to turn off link during a
/// driver unload, or wake on lan is not enabled, remove the link.
pub(super) fn igc_power_down_phy_copper_base(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    // If the management interface is not enabled, then power down
    if ops.check_reset_block(info).is_ok() {
        igc_power_down_phy_copper(ops, info, hw)?;
    }

    Ok(())
}
