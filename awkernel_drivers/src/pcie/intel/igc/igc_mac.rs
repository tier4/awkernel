use awkernel_lib::{delay::wait_millisec, net::ether::ETHER_ADDR_LEN};

use crate::pcie::{
    intel::igc::igc_hw::{IGC_ALT_MAC_ADDRESS_OFFSET_LAN1, IGC_FUNC_1},
    PCIeInfo,
};

use super::{
    igc_defines::*,
    igc_hw::{IgcHw, IgcOperations},
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
