use crate::pcie::PCIeInfo;

use super::{igc_defines::*, igc_regs::*, read_reg, write_reg, IgcDriverErr};

/// Disables PCI-Express master access and verifies there are no pending
pub(super) fn igc_disable_pcie_master_generic(info: &mut PCIeInfo) -> Result<(), IgcDriverErr> {
    let mut timeout = MASTER_DISABLE_TIMEOUT;

    let mut ctrl = read_reg(info, IGC_CTRL)?;
    ctrl |= IGC_CTRL_GIO_MASTER_DISABLE;
    write_reg(info, IGC_CTRL, ctrl)?;

    while timeout > 0 {
        if read_reg(info, IGC_STATUS)? & IGC_STATUS_GIO_MASTER_ENABLE == 0 {
            break;
        }
        awkernel_lib::delay::wait_microsec(100);
        timeout -= 1;
    }

    if timeout == 0 {
        return Err(IgcDriverErr::MasterRequestsPending);
    }

    Ok(())
}
