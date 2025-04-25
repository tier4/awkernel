use awkernel_lib::{delay::wait_millisec, net::ether::ETHER_ADDR_LEN};

use crate::pcie::{
    intel::igc::igc_hw::{IGC_ALT_MAC_ADDRESS_OFFSET_LAN1, IGC_FUNC_1},
    PCIeInfo,
};

use super::{
    igc_defines::*,
    igc_hw::{IgcFcMode, IgcHw, IgcOperations},
    igc_regs::*,
    read_reg, write_reg, IgcDriverErr,
};

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

/// Check for alternate MAC addr
///
/// Checks the nvm for an alternate MAC address.  An alternate MAC address
/// can be setup by pre-boot software and must be treated like a permanent
/// address and must override the actual permanent MAC address. If an
/// alternate MAC address is found it is programmed into RAR0, replacing
/// the permanent address that was installed into RAR0 by the Si on reset.
/// This function will return SUCCESS unless it encounters an error while
/// reading the EEPROM.
pub(super) fn igc_check_alt_mac_addr_generic(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    let mut nvm_data = [0];
    ops.read(info, hw, NVM_COMPAT, 1, &mut nvm_data)?;

    let mut nvm_alt_mac_addr_offset = [0; 1];
    ops.read(
        info,
        hw,
        NVM_ALT_MAC_ADDR_PTR,
        1,
        &mut nvm_alt_mac_addr_offset,
    )?;

    if nvm_alt_mac_addr_offset[0] == 0xFFFF || nvm_alt_mac_addr_offset[0] == 0x0000 {
        // There is no Alternate MAC Address
        return Ok(());
    }

    if hw.bus.func == IGC_FUNC_1 {
        nvm_alt_mac_addr_offset[0] += IGC_ALT_MAC_ADDRESS_OFFSET_LAN1;
    }

    let mut alt_mac_addr = [0; ETHER_ADDR_LEN];
    for i in (0..ETHER_ADDR_LEN as u16).step_by(2) {
        let offset = nvm_alt_mac_addr_offset[0] + (i >> 1);
        ops.read(info, hw, offset, 1, &mut nvm_data)?;
        alt_mac_addr[i as usize] = (nvm_data[0] & 0xFF) as u8;
        alt_mac_addr[i as usize + 1] = (nvm_data[0] >> 8) as u8;
    }

    // if multicast bit is set, the alternate address will not be used
    if alt_mac_addr[0] & 0x01 != 0 {
        return Ok(());
    }

    // We have a valid alternate MAC address, and we want to treat it the
    // same as the normal permanent MAC address stored by the HW into the
    // RAR. Do this by mapping this address into RAR0.
    ops.rar_set(info, hw, &alt_mac_addr, 0)?;

    Ok(())
}

/// Check for auto read completion
/// Check EEPROM for Auto Read done bit.
pub(super) fn igc_get_auto_rd_done_generic(info: &mut PCIeInfo) -> Result<(), IgcDriverErr> {
    for _ in 0..AUTO_READ_DONE_TIMEOUT {
        if read_reg(info, IGC_EECD)? & IGC_EECD_AUTO_RD != 0 {
            return Ok(());
        }
        wait_millisec(1);
    }

    log::debug!("Auto read by HW from NVM has not completed.");
    Err(IgcDriverErr::Reset)
}

/// Release hardware semaphore used to access the PHY or NVM
pub(super) fn igc_put_hw_semaphore_generic(info: &mut PCIeInfo) -> Result<(), IgcDriverErr> {
    let mut swsm = read_reg(info, IGC_SWSM)?;
    swsm &= !(IGC_SWSM_SMBI | IGC_SWSM_SWESMBI);

    write_reg(info, IGC_SWSM, swsm)
}

pub(super) fn igc_setup_link_generic(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    // In the case of the phy reset being blocked, we already have a link.
    // We do not need to set it up again.
    match ops.check_reset_block(info) {
        Ok(_) => (),
        Err(IgcDriverErr::BlkPhyReset) => return Ok(()),
        Err(e) => return Err(e),
    }

    // If requested flow control is set to default, set flow control
    // for both 'rx' and 'tx' pause frames.
    if hw.fc.requested_mode == IgcFcMode::Default {
        hw.fc.requested_mode = IgcFcMode::Full;
    }

    // Save off the requested flow control mode for use later.  Depending
    // on the link partner's capabilities, we may or may not use this mode.
    hw.fc.current_mode = hw.fc.requested_mode;

    // Call the necessary media_type subroutine to configure the link.
    ops.setup_physical_interface(info, hw)?;

    // Initialize the flow control address, type, and PAUSE timer
    // registers to their default values.  This is done even if flow
    // control is disabled, because it does not hurt anything to
    // initialize these registers.
    write_reg(info, IGC_FCT, FLOW_CONTROL_TYPE)?;
    write_reg(info, IGC_FCAH, FLOW_CONTROL_ADDRESS_HIGH)?;
    write_reg(info, IGC_FCAL, FLOW_CONTROL_ADDRESS_LOW)?;

    write_reg(info, IGC_FCTTV, hw.fc.pause_time as u32)?;

    igc_set_fc_watermarks_generic(info, hw)
}

///  Sets the flow control high/low threshold (watermark) registers.  If
///  flow control XON frame transmission is enabled, then set XON frame
///  transmission as well.
fn igc_set_fc_watermarks_generic(info: &mut PCIeInfo, hw: &IgcHw) -> Result<(), IgcDriverErr> {
    let mut fcrtl = 0;
    let mut fcrth = 0;

    // Set the flow control receive threshold registers.  Normally,
    // these registers will be set to a default threshold that may be
    // adjusted later by the driver's runtime code.  However, if the
    // ability to transmit pause frames is not enabled, then these
    // registers will be set to 0.
    if hw.fc.current_mode.contains(IgcFcMode::TxPause) {
        // We need to set up the Receive Threshold high and low water
        // marks as well as (optionally) enabling the transmission of
        // XON frames.
        fcrtl = hw.fc.low_water;
        if hw.fc.send_xon {
            fcrtl |= IGC_FCRTL_XONE;
        }

        fcrth = hw.fc.high_water;
    }

    write_reg(info, IGC_FCRTL, fcrtl)?;
    write_reg(info, IGC_FCRTH, fcrth)?;

    Ok(())
}
