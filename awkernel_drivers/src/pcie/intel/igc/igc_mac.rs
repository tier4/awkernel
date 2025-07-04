use awkernel_lib::{delay::wait_millisec, net::ether::ETHER_ADDR_LEN};

use crate::pcie::{
    intel::igc::igc_hw::{IGC_ALT_MAC_ADDRESS_OFFSET_LAN1, IGC_FUNC_1},
    PCIeInfo,
};

use super::{
    igc_defines::*,
    igc_hw::{IgcFcMode, IgcHw, IgcOperations},
    igc_regs::*,
    read_reg, write_reg, IgcDriverErr, IgcMacType,
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

/// Setup the receive address registers by setting the base receive address
/// register to the devices MAC address and clearing all the other receive
/// address registers to 0.
pub(super) fn igc_init_rx_addrs_generic(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    rar_count: u16,
) -> Result<(), IgcDriverErr> {
    // Setup the receive address

    let mac_addr = hw.mac.addr;
    ops.rar_set(info, hw, &mac_addr, 0)?;

    // Zero out the other (rar_entry_count - 1) receive addresses
    let mac_addr = [0; ETHER_ADDR_LEN];
    for i in 1..rar_count {
        ops.rar_set(info, hw, &mac_addr, i as usize)?;
    }

    Ok(())
}

/// igc_config_fc_after_link_up_generic - Configures flow control after link
/// @hw: pointer to the HW structure
///
/// Checks the status of auto-negotiation after link up to ensure that the
/// speed and duplex were not forced.  If the link needed to be forced, then
/// flow control needs to be forced also.  If auto-negotiation is enabled
/// and did not fail, then we configure flow control based on our link
/// partner.
pub(super) fn igc_config_fc_after_link_up_generic(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    // Check for the case where we have copper media and auto-neg is
    // enabled.  In this case, we need to check and see if Auto-Neg
    // has completed, and if so, how the PHY and link partner has
    // flow control configured.
    if hw.mac.autoneg {
        // Read the MII Status Register and check to see if AutoNeg
        // has completed.  We read this twice because this reg has
        // some "sticky" (latched) bits.
        let _mii_status_reg = ops.read_reg(info, hw, PHY_STATUS)?;
        let mii_status_reg = ops.read_reg(info, hw, PHY_STATUS)?;

        if mii_status_reg & MII_SR_AUTONEG_COMPLETE == 0 {
            return Ok(());
        }

        // The AutoNeg process has completed, so we now need to
        // read both the Auto Negotiation Advertisement
        // Register (Address 4) and the Auto_Negotiation Base
        // Page Ability Register (Address 5) to determine how
        // flow control was negotiated.
        let mii_nway_adv_reg = ops.read_reg(info, hw, PHY_AUTONEG_ADV)?;
        let mii_nway_lp_ability_reg = ops.read_reg(info, hw, PHY_LP_ABILITY)?;

        // Two bits in the Auto Negotiation Advertisement Register
        // (Address 4) and two bits in the Auto Negotiation Base
        // Page Ability Register (Address 5) determine flow control
        // for both the PHY and the link partner.  The following
        // table, taken out of the IEEE 802.3ab/D6.0 dated March 25,
        // 1999, describes these PAUSE resolution bits and how flow
        // control is determined based upon these settings.
        // NOTE:  DC = Don't Care
        //
        //   LOCAL DEVICE  |   LINK PARTNER
        // PAUSE | ASM_DIR | PAUSE | ASM_DIR | NIC Resolution
        //-------|---------|-------|---------|--------------------
        //   0   |    0    |  DC   |   DC    | igc_fc_none
        //   0   |    1    |   0   |   DC    | igc_fc_none
        //   0   |    1    |   1   |    0    | igc_fc_none
        //   0   |    1    |   1   |    1    | igc_fc_tx_pause
        //   1   |    0    |   0   |   DC    | igc_fc_none
        //   1   |   DC    |   1   |   DC    | igc_fc_full
        //   1   |    1    |   0   |    0    | igc_fc_none
        //   1   |    1    |   0   |    1    | igc_fc_rx_pause
        //
        // Are both PAUSE bits set to 1?  If so, this implies
        // Symmetric Flow Control is enabled at both ends.  The
        // ASM_DIR bits are irrelevant per the spec.
        //
        // For Symmetric Flow Control:
        //
        //   LOCAL DEVICE  |   LINK PARTNER
        // PAUSE | ASM_DIR | PAUSE | ASM_DIR | Result
        //-------|---------|-------|---------|--------------------
        //   1   |   DC    |   1   |   DC    | IGC_fc_full
        if (mii_nway_adv_reg & NWAY_AR_PAUSE != 0)
            && (mii_nway_lp_ability_reg & NWAY_LPAR_PAUSE != 0)
        {
            // Now we need to check if the user selected Rx ONLY
            // of pause frames.  In this case, we had to advertise
            // FULL flow control because we could not advertise Rx
            // ONLY. Hence, we must now check to see if we need to
            // turn OFF the TRANSMISSION of PAUSE frames.
            if hw.fc.requested_mode == IgcFcMode::Full {
                hw.fc.current_mode = IgcFcMode::Full;
            } else {
                hw.fc.current_mode = IgcFcMode::RxPause;
            }
        }
        // For receiving PAUSE frames ONLY.
        //
        //   LOCAL DEVICE  |   LINK PARTNER
        // PAUSE | ASM_DIR | PAUSE | ASM_DIR | Result
        //-------|---------|-------|---------|--------------------
        //   0   |    1    |   1   |    1    | igc_fc_tx_pause
        else if (mii_nway_adv_reg & NWAY_AR_PAUSE == 0)
            && (mii_nway_adv_reg & NWAY_AR_ASM_DIR != 0)
            && (mii_nway_lp_ability_reg & NWAY_LPAR_PAUSE != 0)
            && (mii_nway_lp_ability_reg & NWAY_LPAR_ASM_DIR != 0)
        {
            hw.fc.current_mode = IgcFcMode::TxPause;
        }
        // For transmitting PAUSE frames ONLY.
        //
        //   LOCAL DEVICE  |   LINK PARTNER
        // PAUSE | ASM_DIR | PAUSE | ASM_DIR | Result
        //-------|---------|-------|---------|--------------------
        //   1   |    1    |   0   |    1    | igc_fc_rx_pause
        else if (mii_nway_adv_reg & NWAY_AR_PAUSE != 0)
            && (mii_nway_adv_reg & NWAY_AR_ASM_DIR != 0)
            && (mii_nway_lp_ability_reg & NWAY_LPAR_PAUSE == 0)
            && (mii_nway_lp_ability_reg & NWAY_LPAR_ASM_DIR != 0)
        {
            hw.fc.current_mode = IgcFcMode::RxPause;
        } else {
            // Per the IEEE spec, at this point flow control
            // should be disabled.
            hw.fc.current_mode = IgcFcMode::None;
        }

        // Now we need to do one last check...  If we auto-
        // negotiated to HALF DUPLEX, flow control should not be
        // enabled per IEEE 802.3 spec.
        let (_speed, dupex) = ops.get_link_up_info(info, hw)?;

        if dupex == IgcDuplex::Half {
            hw.fc.current_mode = IgcFcMode::None;
        }

        // Now we call a subroutine to actually force the MAC
        // controller to use the correct flow control settings.
        igc_force_mac_fc_generic(info, hw)?;
    }

    Ok(())
}

/// igc_force_mac_fc_generic - Force the MAC's flow control settings
/// @hw: pointer to the HW structure
//
/// Force the MAC's flow control settings.  Sets the TFCE and RFCE bits in the
/// device control register to reflect the adapter settings.  TFCE and RFCE
/// need to be explicitly set by software when a copper PHY is used because
/// autonegotiation is managed by the PHY rather than the MAC.  Software must
/// also configure these bits when link is forced on a fiber connection.
fn igc_force_mac_fc_generic(info: &mut PCIeInfo, hw: &IgcHw) -> Result<(), IgcDriverErr> {
    let mut ctrl = read_reg(info, IGC_CTRL)?;

    // Because we didn't get link via the internal auto-negotiation
    // mechanism (we either forced link or we got link via PHY
    // auto-neg), we have to manually enable/disable transmit an
    // receive flow control.
    //
    // The "Case" statement below enables/disable flow control
    // according to the "hw->fc.current_mode" parameter.
    //
    // The possible values of the "fc" parameter are:
    //      0:  Flow control is completely disabled
    //      1:  Rx flow control is enabled (we can receive pause
    //          frames but not send pause frames).
    //      2:  Tx flow control is enabled (we can send pause frames
    //          frames but we do not receive pause frames).
    //      3:  Both Rx and Tx flow control (symmetric) is enabled.
    //  other:  No other values should be possible at this point.

    match hw.fc.current_mode {
        IgcFcMode::None => {
            ctrl &= !(IGC_CTRL_TFCE | IGC_CTRL_RFCE);
        }
        IgcFcMode::RxPause => {
            ctrl &= !IGC_CTRL_TFCE;
            ctrl |= IGC_CTRL_RFCE;
        }
        IgcFcMode::TxPause => {
            ctrl &= !IGC_CTRL_RFCE;
            ctrl |= IGC_CTRL_TFCE;
        }
        IgcFcMode::Full => {
            ctrl |= IGC_CTRL_TFCE | IGC_CTRL_RFCE;
        }
        _ => {
            log::error!("Flow control param set incorrectly");
            return Err(IgcDriverErr::Config);
        }
    }

    write_reg(info, IGC_CTRL, ctrl)?;

    Ok(())
}

///  igc_get_speed_and_duplex_copper_generic - Retrieve current speed/duplex
///  @hw: pointer to the HW structure
///  @speed: stores the current speed
///  @duplex: stores the current duplex
///
///  Read the status register for the current speed/duplex and store the current
///  speed and duplex for copper connections.
pub(super) fn igc_get_speed_and_duplex_copper_generic(
    info: &mut PCIeInfo,
    hw: &IgcHw,
) -> Result<(IgcSpeed, IgcDuplex), IgcDriverErr> {
    let status = read_reg(info, IGC_STATUS)?;

    let speed = if status & IGC_STATUS_SPEED_1000 != 0 {
        // For I225, STATUS will indicate 1G speed in both 1 Gbps
        // and 2.5 Gbps link modes. An additional bit is used
        // to differentiate between 1 Gbps and 2.5 Gbps.
        if (hw.mac.mac_type == IgcMacType::I225) && (status & IGC_STATUS_SPEED_2500 != 0) {
            IgcSpeed::Speed2500
        } else {
            IgcSpeed::Speed1000
        }
    } else if status & IGC_STATUS_SPEED_100 != 0 {
        IgcSpeed::Speed100
    } else {
        IgcSpeed::Speed10
    };

    let duplex = if status & IGC_STATUS_FD != 0 {
        IgcDuplex::Full
    } else {
        IgcDuplex::Half
    };

    Ok((speed, duplex))
}

/// Generates a multicast address hash value which is used to determine
/// the multicast filter table array address and new table value.
pub(super) fn igc_hash_mc_addr_generic(hw: &IgcHw, mc_addr: &[u8; ETHER_ADDR_LEN]) -> u32 {
    // Register count multiplied by bits per register
    let hash_mask = ((hw.mac.mta_reg_count * 32) - 1) as u32;

    // For a mc_filter_type of 0, bit_shift is the number of left-shifts
    // where 0xFF would still fall within the hash mask.
    let mut bit_shift = 0;
    while hash_mask >> bit_shift != 0xFF {
        bit_shift += 1;
    }

    // The portion of the address that is used for the hash table
    // is determined by the mc_filter_type setting.
    // The algorithm is such that there is a total of 8 bits of shifting.
    // The bit_shift for a mc_filter_type of 0 represents the number of
    // left-shifts where the MSB of mc_addr[5] would still fall within
    // the hash_mask.  Case 0 does this exactly.  Since there are a total
    // of 8 bits of shifting, then mc_addr[4] will shift right the
    // remaining number of bits. Thus 8 - bit_shift.  The rest of the
    // cases are a variation of this algorithm...essentially raising the
    // number of bits to shift mc_addr[5] left, while still keeping the
    // 8-bit shifting total.
    //
    // For example, given the following Destination MAC Address and an
    // mta register count of 128 (thus a 4096-bit vector and 0xFFF mask),
    // we can see that the bit_shift for case 0 is 4.  These are the hash
    // values resulting from each mc_filter_type...
    // [0] [1] [2] [3] [4] [5]
    // 01  AA  00  12  34  56
    // LSB           MSB
    //
    // case 0: hash_value = ((0x34 >> 4) | (0x56 << 4)) & 0xFFF = 0x563
    // case 1: hash_value = ((0x34 >> 3) | (0x56 << 5)) & 0xFFF = 0xAC6
    // case 2: hash_value = ((0x34 >> 2) | (0x56 << 6)) & 0xFFF = 0x163
    // case 3: hash_value = ((0x34 >> 0) | (0x56 << 8)) & 0xFFF = 0x634

    match hw.mac.mc_filter_type {
        1 => bit_shift += 1,
        2 => bit_shift += 2,
        3 => bit_shift += 4,
        _ => (),
    }

    hash_mask & ((mc_addr[4] as u32 >> (8 - bit_shift)) | ((mc_addr[5] as u32) << bit_shift))
}

/// Clears the base hardware counters by reading the counter registers.
pub(super) fn igc_clear_hw_cntrs_base_generic(info: &PCIeInfo) -> Result<(), IgcDriverErr> {
    // Read all the base hardware counters to clear them.
    for reg in [
        IGC_CRCERRS,
        IGC_MPC,
        IGC_SCC,
        IGC_ECOL,
        IGC_MCC,
        IGC_LATECOL,
        IGC_COLC,
        IGC_RERC,
        IGC_DC,
        IGC_RLEC,
        IGC_XONRXC,
        IGC_XONTXC,
        IGC_XOFFRXC,
        IGC_XOFFTXC,
        IGC_FCRUC,
        IGC_GPRC,
        IGC_BPRC,
        IGC_MPRC,
        IGC_GPTC,
        IGC_GORCL,
        IGC_GORCH,
        IGC_GOTCL,
        IGC_GOTCH,
        IGC_RNBC,
        IGC_RUC,
        IGC_RFC,
        IGC_ROC,
        IGC_RJC,
        IGC_TORL,
        IGC_TORH,
        IGC_TOTL,
        IGC_TOTH,
        IGC_TPR,
        IGC_TPT,
        IGC_MPTC,
        IGC_BPTC,
        IGC_TLPIC,
        IGC_RLPIC,
        IGC_RXDMTC,
    ] {
        read_reg(info, reg)?;
    }

    Ok(())
}
