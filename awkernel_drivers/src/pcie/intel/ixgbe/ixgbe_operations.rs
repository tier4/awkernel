use super::{
    ixgbe_hw::{self, IxgbeBusInfo, IxgbeEepromInfo},
    ixgbe_regs::*,
    IxgbeDriverErr::{self, *},
};
use crate::pcie::{capability::pcie_cap::PCIeCap, PCIeInfo};
use awkernel_lib::delay::{wait_microsec, wait_millisec};
use ixgbe_hw::{EepromType, IxgbeHw, MacType, MediaType, PhyType, SfpType};

/// clear_tx_pending - Clear pending TX work from the PCIe fifo
/// The 82599 and x540 MACs can experience issues if TX work is still pending
/// when a reset occurs.  This function prevents this by flushing the PCIe
/// buffers on the system.
pub fn clear_tx_pending(info: &mut PCIeInfo, hw: &IxgbeHw) -> Result<(), IxgbeDriverErr> {
    use crate::pcie::capability::pcie_cap::registers::DeviceStatusControl;

    // If double reset is not requested then all transactions should
    // already be clear and as such there is no work to do
    if hw.mac.flags & IXGBE_FLAGS_DOUBLE_RESET_REQUIRED == 0 {
        return Ok(());
    }

    // Set loopback enable to prevent any transmits from being sent
    // should the link come up.  This assumes that the RXCTRL.RXEN bit
    // has already been cleared.
    let hlreg0 = ixgbe_hw::read_reg(info, IXGBE_HLREG0)?;
    ixgbe_hw::write_reg(info, IXGBE_HLREG0, hlreg0 | IXGBE_HLREG0_LPBK)?;

    // Wait for a last completion before clearing buffers
    ixgbe_hw::write_flush(info)?;
    wait_millisec(3);

    // Before proceeding, make sure that the PCIe block does not have
    // transactions pending.
    let Some(cap) = info.get_pcie_cap_mut() else {
        return Err(NotPciExpress);
    };
    let poll = pcie_timeout_poll(cap);
    let mut devstatus;
    let mut transactions_pend;
    for _ in 0..poll {
        wait_microsec(100);
        devstatus = cap.get_device_status_control();
        transactions_pend = (devstatus & DeviceStatusControl::TRANSACTIONS_PEND).bits();
        if transactions_pend == 0 {
            break;
        }
    }

    // initiate cleaning flow for buffers in the PCIe transaction layer
    let gcr_ext = ixgbe_hw::read_reg(info, IXGBE_GCR_EXT)?;
    ixgbe_hw::write_reg(
        info,
        IXGBE_GCR_EXT,
        gcr_ext | IXGBE_GCR_EXT_BUFFERS_CLEAR as u32,
    )?;

    // Flush all writes and allow 20usec for all transactions to clear
    ixgbe_hw::write_flush(info)?;
    wait_microsec(20);

    // restore previous register values
    ixgbe_hw::write_reg(info, IXGBE_GCR_EXT, gcr_ext)?;
    ixgbe_hw::write_reg(info, IXGBE_HLREG0, hlreg0)?;
    Ok(())
}

// MAC Helper Functions

/// start_hw_generic - Prepare hardware for Tx/Rx
/// Starts the hardware by filling the bus info structure and media type, clears
/// all on chip counters, initializes receive address registers, multicast
/// table, VLAN filter table, calls routine to set up link and flow control
/// settings, and leaves transmit and receive units disabled and uninitialized
pub fn start_hw_generic<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    use ixgbe_hw::MacType::*;
    // Set the media type
    hw.phy.media_type = ops.mac_get_media_type(info, hw);

    // PHY ops initialization must be done in reset_hw()

    // Clear the VLAN filter table
    ops.mac_clear_vfta(info, hw)?;

    // Clear statistics registers
    ops.mac_clear_hw_cntrs(info, hw)?;

    // Set No Snoop Disable
    let mut ctrl_ext = ixgbe_hw::read_reg(info, IXGBE_CTRL_EXT)?;
    ctrl_ext |= IXGBE_CTRL_EXT_NS_DIS;
    ixgbe_hw::write_reg(info, IXGBE_CTRL_EXT, ctrl_ext)?;
    ixgbe_hw::write_flush(info)?;

    // Setup flow control
    ops.mac_setup_fc(info, hw)?;

    // Cache bit indicating need for crosstalk fix
    let crosstalk_fix = match hw.mac.mac_type {
        IxgbeMac82599EB | IxgbeMacX550EMX | IxgbeMacX550EMA => {
            let device_caps = ops.mac_get_device_caps(info)?;
            device_caps & IXGBE_DEVICE_CAPS_NO_CROSSTALK_WR == 0
        }
        _ => false,
    };

    hw.crosstalk_fix = crosstalk_fix;

    // Clear adapter stopped flag
    hw.adapter_stopped = false;

    Ok(())
}

/// start_hw_gen2 - Init sequence for common device family
/// Performs the init sequence common to the second generation
/// of 10 GbE devices.
/// Devices in the second generation:
///    82599
///    X540
pub fn start_hw_gen2(info: &PCIeInfo, hw: &IxgbeHw) -> Result<(), IxgbeDriverErr> {
    // Clear the rate limiters
    for i in 0..hw.mac.max_tx_queues {
        ixgbe_hw::write_reg(info, IXGBE_RTTDQSEL, i)?;
        ixgbe_hw::write_reg(info, IXGBE_RTTBCNRC, 0)?;
    }
    ixgbe_hw::write_flush(info)?;

    // Disable relaxed ordering
    let mut regval;
    for i in 0..hw.mac.max_tx_queues {
        regval = ixgbe_hw::read_reg(info, IXGBE_DCA_TXCTRL_82599(i as usize))?;
        regval &= !IXGBE_DCA_TXCTRL_DESC_WRO_EN;
        ixgbe_hw::write_reg(info, IXGBE_DCA_TXCTRL_82599(i as usize), regval)?;
    }

    for i in 0..hw.mac.max_rx_queues {
        regval = ixgbe_hw::read_reg(info, IXGBE_DCA_RXCTRL(i as usize))?;
        regval &= !(IXGBE_DCA_RXCTRL_DATA_WRO_EN | IXGBE_DCA_RXCTRL_HEAD_WRO_EN);
        ixgbe_hw::write_reg(info, IXGBE_DCA_RXCTRL(i as usize), regval)?;
    }

    Ok(())
}

/// validate_mac_addr - Validate MAC address
/// Tests a MAC address to ensure it is a valid Individual Address
fn validate_mac_addr(mac_addr: &[u8]) -> Result<(), IxgbeDriverErr> {
    // Make sure it is not a multicast address
    if ixgbe_is_multicast(mac_addr) {
        log::trace!("MAC address is multicast");
        Err(InvalidMacAddr)
    // Not a broadcast address
    } else if ixgbe_is_broadcast(mac_addr) {
        log::trace!("MAC address is broadcast");
        Err(InvalidMacAddr)
    // Reject the zero address
    } else if mac_addr[0] == 0
        && mac_addr[1] == 0
        && mac_addr[2] == 0
        && mac_addr[3] == 0
        && mac_addr[4] == 0
        && mac_addr[5] == 0
    {
        log::trace!("MAC address is all zeros");
        Err(InvalidMacAddr)
    } else {
        Ok(())
    }
}

/// pcie_timeout_poll - Return number of times to poll for completion
/// System-wide timeout range is encoded in PCIe Device Control2 register.
/// Add 10% to specified maximum and return the number of times to poll for
/// completion timeout, in units of 100 microsec.  Never return less than
/// 800 = 80 millisec.
fn pcie_timeout_poll(cap: &mut PCIeCap) -> u32 {
    use crate::pcie::capability::pcie_cap::registers::DeviceStatusControl2;
    let devctl2 = cap.get_device_status_control2();

    let cpl_timeout_value = (devctl2 & DeviceStatusControl2::CPL_TIMEOUT_VALUE).bits();
    let pollcnt = match cpl_timeout_value {
        IXGBE_PCIDEVCTRL2_65_130MS => 1300,  // 130 millisec
        IXGBE_PCIDEVCTRL2_260_520MS => 5200, // 520 millisec
        IXGBE_PCIDEVCTRL2_1_2S => 20000,     // 2 sec
        IXGBE_PCIDEVCTRL2_4_8S => 80000,     // 8 sec
        IXGBE_PCIDEVCTRL2_17_34S => 340000,  // 34 sec
        IXGBE_PCIDEVCTRL2_50_100US
        | IXGBE_PCIDEVCTRL2_1_2MS
        | IXGBE_PCIDEVCTRL2_16_32MS
        | IXGBE_PCIDEVCTRL2_16_32MS_DEF => 800, // 80 millisec minimum
        _ => 800,                            // Default case
    };

    // add 10% to spec maximum
    (pollcnt * 11) / 10
}

/// disable_pcie_master - Disable PCI-express master access
/// Disables PCI-Express master access and verifies there are no pending
/// requests. IXGBE_ERR_MASTER_REQUESTS_PENDING is returned if master disable
/// bit hasn't caused the master requests to be disabled, else IXGBE_SUCCESS
/// is returned signifying master requests disabled.
fn disable_pcie_master(info: &mut PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
    use crate::pcie::capability::pcie_cap::registers::DeviceStatusControl;
    // Always set this bit to ensure any future transactions are blocked
    ixgbe_hw::write_reg(info, IXGBE_CTRL, IXGBE_CTRL_GIO_DIS)?;

    // Exit if master requests are blocked
    let mut status = ixgbe_hw::read_reg(info, IXGBE_STATUS)?;
    if status & IXGBE_STATUS_GIO == 0 {
        return Ok(());
    }

    // Poll for master request bit to clear
    for _ in 0..IXGBE_PCI_MASTER_DISABLE_TIMEOUT {
        wait_microsec(100);
        status = ixgbe_hw::read_reg(info, IXGBE_STATUS)?;
        if status & IXGBE_STATUS_GIO == 0 {
            return Ok(());
        }
    }

    // Two consecutive resets are required via CTRL.RST per datasheet
    // 5.2.5.3.2 Master Disable.  We set a flag to inform the reset routine
    // of this need.  The first reset prevents new master requests from
    // being issued by our device.  We then must wait 1usec or more for any
    // remaining completions from the PCIe bus to trickle in, and then reset
    // again to clear out any effects they may have had on our device.
    //
    log::debug!("GIO Master Disable bit didn't clear - requesting resets\n");
    hw.mac.flags |= IXGBE_FLAGS_DOUBLE_RESET_REQUIRED;

    if hw.mac.mac_type >= MacType::IxgbeMacX550 {
        return Ok(());
    }

    // Before proceeding, make sure that the PCIe block does not have
    // transactions pending.
    let Some(cap) = info.get_pcie_cap_mut() else {
        return Err(NotPciExpress);
    };
    let poll = pcie_timeout_poll(cap);

    let mut devstatus;
    let mut transactions_pend;
    for _ in 0..poll {
        wait_microsec(100);
        devstatus = cap.get_device_status_control();
        transactions_pend = (devstatus & DeviceStatusControl::TRANSACTIONS_PEND).bits();
        if transactions_pend == 0 {
            return Ok(());
        }
    }

    log::error!("PCIe transaction pending bit also did not clear.\n");
    Err(MasterRequestsPending)
}

/// set_pci_config_data - Generic store PCI bus info
/// Stores the PCI bus info (speed, width, type) within the ixgbe_hw structure
fn set_pci_config_data<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
    link_status: u16,
) -> Result<IxgbeBusInfo, IxgbeDriverErr> {
    use ixgbe_hw::{BusSpeed::*, BusType::*, BusWidth::*};

    let mut bus_type = hw.bus.bus_type;
    if bus_type == IxgbeBusTypeUnknown {
        bus_type = IxgbeBusTypePciExpress;
    }

    let width = match link_status as u32 & IXGBE_PCI_LINK_WIDTH {
        IXGBE_PCI_LINK_WIDTH_1 => IxgbeBusWidthPcieX1,
        IXGBE_PCI_LINK_WIDTH_2 => IxgbeBusWidthPcieX2,
        IXGBE_PCI_LINK_WIDTH_4 => IxgbeBusWidthPcieX4,
        IXGBE_PCI_LINK_WIDTH_8 => IxgbeBusWidthPcieX8,
        _ => IxgbeBusWidthUnknown,
    };

    let speed = match link_status as u32 & IXGBE_PCI_LINK_SPEED {
        IXGBE_PCI_LINK_SPEED_2500 => IxgbeBusSpeed2500,
        IXGBE_PCI_LINK_SPEED_5000 => IxgbeBusSpeed5000,
        IXGBE_PCI_LINK_SPEED_8000 => IxgbeBusSpeed8000,
        _ => IxgbeBusSpeedUnknown,
    };

    let (func, lan_id, instance_id) = ops.mac_set_lan_id(info, hw)?;
    let businfo = IxgbeBusInfo {
        speed,
        width,
        bus_type,
        func,
        lan_id,
        instance_id,
    };

    Ok(businfo)
}

/// device_supports_autoneg_fc - Check if device supports autonegotiation
/// This function returns TRUE if the device supports flow control
/// autonegotiation, and FALSE if it does not.
fn device_supports_autoneg_fc<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<bool, IxgbeDriverErr> {
    use ixgbe_hw::MediaType::*;

    let supported = match hw.phy.media_type {
        IxgbeMediaTypeFiberFixed | IxgbeMediaTypeFiberQsfp | IxgbeMediaTypeFiber => {
            // flow control autoneg black list
            match info.id {
                IXGBE_DEV_ID_X550EM_A_SFP
                | IXGBE_DEV_ID_X550EM_A_SFP_N
                | IXGBE_DEV_ID_X550EM_A_QSFP
                | IXGBE_DEV_ID_X550EM_A_QSFP_N => false,
                _ => {
                    let (speed, link_up) = ops.mac_check_link(info, hw, false)?;
                    if link_up {
                        speed == IXGBE_LINK_SPEED_1GB_FULL
                    } else {
                        true
                    }
                }
            }
        }
        IxgbeMediaTypeBackplane => info.id != IXGBE_DEV_ID_X550EM_X_XFI,
        IxgbeMediaTypeCopper => {
            // only some copper devices support flow control autoneg
            matches!(
                info.id,
                IXGBE_DEV_ID_82599_T3_LOM
                    | IXGBE_DEV_ID_X540T
                    | IXGBE_DEV_ID_X540T1
                    | IXGBE_DEV_ID_X540_BYPASS
                    | IXGBE_DEV_ID_X550T
                    | IXGBE_DEV_ID_X550T1
                    | IXGBE_DEV_ID_X550EM_X_10G_T
                    | IXGBE_DEV_ID_X550EM_A_10G_T
                    | IXGBE_DEV_ID_X550EM_A_1G_T
                    | IXGBE_DEV_ID_X550EM_A_1G_T_L
            )
        }
        _ => false,
    };

    if !supported {
        log::error!("Device {:?} does not support flow control autoneg", info.id);
    }

    Ok(supported)
}

fn need_crosstalk_fix<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> bool {
    use ixgbe_hw::MediaType::*;
    // Does FW say we need the fix
    if !hw.crosstalk_fix {
        return false;
    }

    // Only consider SFP+ PHYs i.e. media type fiber
    matches!(
        ops.mac_get_media_type(info, hw),
        IxgbeMediaTypeFiber | IxgbeMediaTypeFiberQsfp
    )
}

fn fc_autoneg_fiber(info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
    // On multispeed fiber at 1g, bail out if
    // - link is up but AN did not complete, or if
    // - link is up and AN completed but timed out
    let linkstat = ixgbe_hw::read_reg(info, IXGBE_PCS1GLSTA)?;
    if (linkstat & IXGBE_PCS1GLSTA_AN_COMPLETE == 0)
        || (linkstat & IXGBE_PCS1GLSTA_AN_TIMED_OUT != 0)
    {
        log::debug!("Auto-Negotiation did not complete or timed out");
        return Err(FcNotNegotiated);
    }

    let pcs_anadv_reg = ixgbe_hw::read_reg(info, IXGBE_PCS1GANA)?;
    let pcs_lpab_reg = ixgbe_hw::read_reg(info, IXGBE_PCS1GANLP)?;

    negotiate_fc(
        hw,
        pcs_anadv_reg,
        pcs_lpab_reg,
        IXGBE_PCS1GANA_SYM_PAUSE,
        IXGBE_PCS1GANA_ASM_PAUSE,
        IXGBE_PCS1GANA_SYM_PAUSE,
        IXGBE_PCS1GANA_ASM_PAUSE,
    )
}

/// fc_autoneg_backplane - Enable flow control IEEE clause 37
/// Enable flow control according to IEEE clause 37.
fn fc_autoneg_backplane(info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
    // On backplane, bail out if
    // - backplane autoneg was not completed, or if
    // - we are 82599 and link partner is not AN enabled
    let links = ixgbe_hw::read_reg(info, IXGBE_LINKS)?;
    if (links & IXGBE_LINKS_KX_AN_COMP) == 0 {
        log::debug!("Auto-Negotiation did not complete");
        return Err(FcNotNegotiated);
    }

    if hw.mac.mac_type == MacType::IxgbeMac82599EB {
        let links2 = ixgbe_hw::read_reg(info, IXGBE_LINKS2)?;
        if (links2 & IXGBE_LINKS2_AN_SUPPORTED) == 0 {
            log::debug!("Link partner is not AN enabled");
            return Err(FcNotNegotiated);
        }
    }

    // Read the 10g AN autoc and LP ability registers and resolve
    // local flow control settings accordingly
    let autoc_reg = ixgbe_hw::read_reg(info, IXGBE_AUTOC)?;
    let anlp1_reg = ixgbe_hw::read_reg(info, IXGBE_ANLP1)?;

    negotiate_fc(
        hw,
        autoc_reg,
        anlp1_reg,
        IXGBE_AUTOC_SYM_PAUSE,
        IXGBE_AUTOC_ASM_PAUSE,
        IXGBE_ANLP1_SYM_PAUSE,
        IXGBE_ANLP1_ASM_PAUSE,
    )
}

/// fc_autoneg_copper - Enable flow control IEEE clause 37
/// Enable flow control according to IEEE clause 37.
fn fc_autoneg_copper<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    let technology_ability_reg = ops.phy_read_reg(
        info,
        hw,
        IXGBE_MDIO_AUTO_NEG_ADVT,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
    )?;
    let lp_technology_ability_reg = ops.phy_read_reg(
        info,
        hw,
        IXGBE_MDIO_AUTO_NEG_LP,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
    )?;

    negotiate_fc(
        hw,
        technology_ability_reg as u32,
        lp_technology_ability_reg as u32,
        IXGBE_TAF_SYM_PAUSE,
        IXGBE_TAF_ASM_PAUSE,
        IXGBE_TAF_SYM_PAUSE,
        IXGBE_TAF_ASM_PAUSE,
    )
}

/// negotiate_fc - Negotiate flow control
/// Find the intersection between advertised settings and link partner's
/// advertised settings
fn negotiate_fc(
    hw: &mut IxgbeHw,
    adv_reg: u32,
    lp_reg: u32,
    adv_sym: u32,
    adv_asm: u32,
    lp_sym: u32,
    lp_asm: u32,
) -> Result<(), IxgbeDriverErr> {
    use ixgbe_hw::FcMode::*;

    if (adv_reg == 0) || (lp_reg == 0) {
        log::error!("Local or link partner's advertised flow control settings are NULL. Local: {:?}, link partner: {:?}", adv_reg, lp_reg);
        return Err(FcNotNegotiated);
    }

    if (adv_reg & adv_sym != 0) && (lp_reg & lp_sym != 0) {
        /*
         * Now we need to check if the user selected Rx ONLY
         * of pause frames.  In this case, we had to advertise
         * FULL flow control because we could not advertise RX
         * ONLY. Hence, we must now check to see if we need to
         * turn OFF the TRANSMISSION of PAUSE frames.
         */
        if hw.fc.requested_mode == IxgbeFcFull {
            hw.fc.current_mode = IxgbeFcFull;
            log::debug!("Flow Control = FULL.");
        } else {
            hw.fc.current_mode = IxgbeFcRxPause;
            log::debug!("Flow Control=RX PAUSE frames only");
        }
    } else if (adv_reg & adv_sym == 0)
        && (adv_reg & adv_asm != 0)
        && (lp_reg & lp_sym != 0)
        && (lp_reg & lp_asm != 0)
    {
        hw.fc.current_mode = IxgbeFcTxPause;
        log::debug!("Flow Control = TX PAUSE frames only.");
    } else if (adv_reg & adv_sym != 0)
        && (adv_reg & adv_asm != 0)
        && (lp_reg & lp_sym == 0)
        && (lp_reg & lp_asm != 0)
    {
        hw.fc.current_mode = IxgbeFcRxPause;
        log::debug!("Flow Control = RX PAUSE frames only.");
    } else {
        hw.fc.current_mode = IxgbeFcNone;
        log::debug!("Flow Control = NONE.");
    }
    Ok(())
}

/// set_mta - Set bit-vector in multicast table
/// Sets the bit-vector in the multicast table.
pub fn set_mta(hw: &mut IxgbeHw, mc_addr: &[u8]) {
    hw.addr_ctrl.mta_in_use += 1;
    let vector = mta_vector(hw, mc_addr);
    // The MTA is a register array of 128 32-bit registers. It is treated
    // like an array of 4096 bits.  We want to set bit
    // BitArray[vector_value]. So we figure out what register the bit is
    // in, read it, OR in the new bit, then write back the new value.  The
    // register is determined by the upper 7 bits of the vector value and
    // the bit within that register are determined by the lower 5 bits of
    // the value.
    let vector_reg = (vector >> 5) & 0x7F;
    let vector_bit = vector & 0x1F;
    hw.mac.mta_shadow[vector_reg as usize] |= 1 << vector_bit
}

/// mta_vector - Determines bit-vector in multicast table to set
/// Extracts the 12 bits, from a multicast address, to determine which
/// bit-vector to set in the multicast table. The hardware uses 12 bits, from
/// incoming rx multicast addresses, to determine the bit-vector to check in
/// the MTA. Which of the 4 combination, of 12-bits, the hardware uses is set
/// by the MO field of the MCSTCTRL. The MO field is set during initialization
/// to mc_filter_type.
pub fn mta_vector(hw: &IxgbeHw, mc_addr: &[u8]) -> u16 {
    let mut vector = match hw.mac.mc_filter_type {
        0 => {
            // use bits [47:36] of the address
            (mc_addr[4] >> 4) as u16 | ((mc_addr[5] as u16) << 4)
        }
        1 => {
            // use bits [46:35] of the address
            (mc_addr[4] >> 3) as u16 | ((mc_addr[5] as u16) << 5)
        }
        2 => {
            // use bits [45:34] of the address
            (mc_addr[4] >> 2) as u16 | ((mc_addr[5] as u16) << 6)
        }
        3 => {
            // use bits [43:32] of the address
            (mc_addr[4]) as u16 | ((mc_addr[5] as u16) << 8)
        }
        _ => {
            // Invalid mc_filter_type
            log::debug!("MC filter type param set incorrectly\n");
            panic!("incorrect multicast filter type");
        }
    };

    // vector can only be 12-bits or boundary will be exceeded
    vector &= 0xFFF;
    vector
}

/// mng_present - returns TRUE when management capability is present
pub fn mng_present(info: &PCIeInfo, hw: &IxgbeHw) -> Result<bool, IxgbeDriverErr> {
    let fwsm_offset = get_fwsm_offset(info.get_id())?;

    if hw.mac.mac_type < MacType::IxgbeMac82599EB {
        return Ok(false);
    }

    let fwsm = ixgbe_hw::read_reg(info, fwsm_offset)?;

    Ok(fwsm & IXGBE_FWSM_FW_MODE_PT != 0)
}

/// disable_tx_laser_multispeed_fiber - Disable Tx laser
/// The base drivers may require better control over SFP+ module
/// PHY states.  This includes selectively shutting down the Tx
/// laser on the PHY, effectively halting physical link.
pub fn disable_tx_laser_multispeed_fiber(
    info: &PCIeInfo,
    hw: &IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    let mut esdp_reg = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;

    // Blocked by MNG FW so bail
    if check_reset_blocked(info, hw)? {
        return Ok(());
    }

    // Disable Tx laser; allow 100us to go dark per spec
    esdp_reg |= IXGBE_ESDP_SDP3;
    ixgbe_hw::write_reg(info, IXGBE_ESDP, esdp_reg)?;
    ixgbe_hw::write_flush(info)?;
    wait_microsec(100);

    Ok(())
}

/// enable_tx_laser_multispeed_fiber - Enable Tx laser
/// The base drivers may require better control over SFP+ module
/// PHY states.  This includes selectively turning on the Tx
/// laser on the PHY, effectively starting physical link.
pub fn enable_tx_laser_multispeed_fiber(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let mut esdp_reg = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;

    // Enable Tx laser; allow 100ms to light up
    esdp_reg &= !IXGBE_ESDP_SDP3;
    ixgbe_hw::write_reg(info, IXGBE_ESDP, esdp_reg)?;
    ixgbe_hw::write_flush(info)?;
    wait_millisec(100);

    Ok(())
}

/// flap_tx_laser - Flap Tx laser
/// When the driver changes the link speeds that it can support,
/// it sets autotry_restart to TRUE to indicate that we need to
/// initiate a new autotry session with the link partner.  To do
/// so, we set the speed then disable and re-enable the Tx laser, to
/// alert the link partner that it also needs to restart autotry on its
/// end.  This is consistent with TRUE clause 37 autoneg, which also
/// involves a loss of signal.
fn flap_tx_laser_multispeed_fiber(info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
    log::debug!("ixgbe_flap_tx_laser_multispeed_fiber");

    // Blocked by MNG FW so bail
    if check_reset_blocked(info, hw)? {
        return Ok(());
    }

    if hw.mac.autotry_restart {
        disable_tx_laser_multispeed_fiber(info, hw)?;
        enable_tx_laser_multispeed_fiber(info)?;
        hw.mac.autotry_restart = false;
    }

    Ok(())
}

/// get_sfp_init_sequence_offsets - Provides offset of PHY init sequence
/// Checks the MAC's EEPROM to see if it supports a given SFP+ module type, if
/// so it returns the offsets to the phy init sequence block.
pub fn get_sfp_init_sequence_offsets<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(u16, u16), IxgbeDriverErr> {
    use SfpType::*;
    let mut sfp_type = hw.phy.sfp_type;

    if sfp_type == IxgbeSfpTypeUnknown {
        return Err(IxgbeDriverErr::SfpNotSupported);
    }

    if sfp_type == IxgbeSfpTypeNotPresent {
        return Err(IxgbeDriverErr::SfpNotPresent);
    }

    if (info.get_id() == IXGBE_DEV_ID_82598_SR_DUAL_PORT_EM)
        && (hw.phy.sfp_type == IxgbeSfpTypeDaCu)
    {
        return Err(IxgbeDriverErr::SfpNotSupported);
    }

    //  Limiting active cables and 1G Phys must be initialized as SR modules
    if sfp_type == IxgbeSfpTypeDaActLmtCore0
        || sfp_type == IxgbeSfpType1gLxCore0
        || sfp_type == IxgbeSfpType1gCuCore0
        || sfp_type == IxgbeSfpType1gSxCore0
    {
        sfp_type = IxgbeSfpTypeSrlrCore0;
    } else if sfp_type == IxgbeSfpTypeDaActLmtCore1
        || sfp_type == IxgbeSfpType1gLxCore1
        || sfp_type == IxgbeSfpType1gCuCore1
        || sfp_type == IxgbeSfpType1gSxCore1
    {
        sfp_type = IxgbeSfpTypeSrlrCore1;
    }

    // Read offset to PHY init contents
    let mut list_offset = [0; 1];
    if ops
        .eeprom_read(
            info,
            &mut hw.eeprom,
            IXGBE_PHY_INIT_OFFSET_NL,
            &mut list_offset,
        )
        .is_err()
    {
        log::error!("eeprom read at offset {} failed", IXGBE_PHY_INIT_OFFSET_NL);
        return Err(SfpNoInitSeqPresent);
    }

    if (list_offset[0] == 0) || (list_offset[0] == 0xFFFF) {
        return Err(IxgbeDriverErr::SfpNoInitSeqPresent);
    }

    // Shift offset to first ID word
    list_offset[0] += 1;

    // Find the matching SFP ID in the EEPROM
    // and program the init sequence
    let mut sfp_id = [0; 1];
    if ops
        .eeprom_read(info, &mut hw.eeprom, list_offset[0], &mut sfp_id)
        .is_err()
    {
        log::error!("eeprom read at offset {} failed", list_offset[0]);
        return Err(IxgbeDriverErr::Phy);
    }

    let mut data_offset = [0; 1];
    while sfp_id[0] != IXGBE_PHY_INIT_END_NL {
        let sfp_id_sfptype = SfpType::try_from(sfp_id[0])?;
        if sfp_id_sfptype == sfp_type {
            list_offset[0] += 1;
            if ops
                .eeprom_read(info, &mut hw.eeprom, list_offset[0], &mut data_offset)
                .is_err()
            {
                log::error!("eeprom read at offset {} failed", list_offset[0]);
                return Err(IxgbeDriverErr::Phy);
            }

            if (data_offset[0] == 0) || (data_offset[0] == 0xFFFF) {
                log::debug!("SFP+ module not supported\n");
                return Err(IxgbeDriverErr::SfpNotSupported);
            } else {
                break;
            }
        } else {
            list_offset[0] += 2;
            if ops
                .eeprom_read(info, &mut hw.eeprom, list_offset[0], &mut sfp_id)
                .is_err()
            {
                log::error!("eeprom read at offset {} failed", list_offset[0]);
                return Err(IxgbeDriverErr::Phy);
            }
        }
    }

    // the 82598EB SFP+ card officially supports only direct attached cables
    // but works fine with optical SFP+ modules as well. Even though the
    // EEPROM has no matching ID for them. So just accept the module.
    if sfp_id[0] == IXGBE_PHY_INIT_END_NL && hw.mac.mac_type == MacType::IxgbeMac82598EB {
        // refetch offset for the first phy entry
        ops.eeprom_read(
            info,
            &mut hw.eeprom,
            IXGBE_PHY_INIT_OFFSET_NL,
            &mut list_offset,
        )?;
        list_offset[0] += 2;
        ops.eeprom_read(info, &mut hw.eeprom, list_offset[0], &mut data_offset)?;
    } else if sfp_id[0] == IXGBE_PHY_INIT_END_NL {
        log::debug!("No matching SFP+ module found\n");
        return Err(IxgbeDriverErr::SfpNotSupported);
    }

    Ok((list_offset[0], data_offset[0]))
}

/// get_copper_link_capabilities - Determines link capabilities
pub fn get_copper_link_capabilities<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(u32, bool), IxgbeDriverErr> {
    if hw.phy.speeds_supported == IXGBE_LINK_SPEED_UNKNOWN {
        get_copper_speeds_supported(ops, info, hw)?;
    }

    let speed = hw.phy.speeds_supported;

    Ok((speed, true))
}

/// get_copper_speeds_supported - Get copper link speeds from phy
/// Determines the supported link capabilities by reading the PHY auto
/// negotiation register.
fn get_copper_speeds_supported<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    use ixgbe_hw::MacType::*;

    let speed_ability = ops.phy_read_reg(
        info,
        hw,
        IXGBE_MDIO_PHY_SPEED_ABILITY,
        IXGBE_MDIO_PMA_PMD_DEV_TYPE,
    )?;

    if speed_ability & IXGBE_MDIO_PHY_SPEED_10G as u16 != 0 {
        hw.phy.speeds_supported |= IXGBE_LINK_SPEED_10GB_FULL;
    }
    if speed_ability & IXGBE_MDIO_PHY_SPEED_1G as u16 != 0 {
        hw.phy.speeds_supported |= IXGBE_LINK_SPEED_1GB_FULL;
    }
    if speed_ability & IXGBE_MDIO_PHY_SPEED_100M as u16 != 0 {
        hw.phy.speeds_supported |= IXGBE_LINK_SPEED_100_FULL;
    }

    match hw.mac.mac_type {
        IxgbeMacX550 => {
            hw.phy.speeds_supported |= IXGBE_LINK_SPEED_2_5GB_FULL;
            hw.phy.speeds_supported |= IXGBE_LINK_SPEED_5GB_FULL;
        }
        IxgbeMacX550EMX | IxgbeMacX550EMA => hw.phy.speeds_supported &= !IXGBE_LINK_SPEED_100_FULL,
        _ => (),
    }

    Ok(())
}

/// stop_mac_link_on_d3_82599 - Disables link on D3
/// Disables link during D3 power down sequence.
pub fn stop_mac_link_on_d3_82599<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    let mut ee_ctrl_2 = [0; 1];
    ops.eeprom_read(info, &mut hw.eeprom, IXGBE_EEPROM_CTRL_2, &mut ee_ctrl_2)?;

    if !mng_present(info, hw)? && (ee_ctrl_2[0] & IXGBE_EEPROM_CCD_BIT != 0) {
        let mut autoc2_reg = ixgbe_hw::read_reg(info, IXGBE_AUTOC2)?;
        autoc2_reg |= IXGBE_AUTOC2_LINK_DISABLE_ON_D3_MASK;
        ixgbe_hw::write_reg(info, IXGBE_AUTOC2, autoc2_reg)?;
    }

    Ok(())
}

/// set_soft_rate_select_speed - Set module link speed
/// Set module link speed via the soft rate select.
pub fn set_soft_rate_select_speed<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &IxgbeHw,
    speed: u32,
) -> Result<(), IxgbeDriverErr> {
    let rs = match speed {
        IXGBE_LINK_SPEED_10GB_FULL => IXGBE_SFF_SOFT_RS_SELECT_10G, // one bit mask same as setting on
        IXGBE_LINK_SPEED_1GB_FULL => IXGBE_SFF_SOFT_RS_SELECT_1G,
        _ => {
            log::debug!("Invalid fixed module speed\n");
            return Ok(());
        }
    };

    // Set RS0
    let mut eeprom_data = match ops.phy_read_i2c_byte(
        info,
        hw,
        IXGBE_SFF_SFF_8472_OSCB,
        IXGBE_I2C_EEPROM_DEV_ADDR2,
    ) {
        Ok(data) => data,
        Err(e) => {
            log::debug!("Failed to read Rx Rate Select RS0\n");
            return Err(e);
        }
    };

    eeprom_data = (eeprom_data & !IXGBE_SFF_SOFT_RS_SELECT_MASK) | rs;

    if let Err(e) = ops.phy_write_i2c_byte(
        info,
        hw,
        IXGBE_SFF_SFF_8472_OSCB,
        IXGBE_I2C_EEPROM_DEV_ADDR2,
        eeprom_data,
    ) {
        log::debug!("Failed to write Rx Rate Select RS0\n");
        return Err(e);
    }

    // Set RS1
    let mut eeprom_data = match ops.phy_read_i2c_byte(
        info,
        hw,
        IXGBE_SFF_SFF_8472_ESCB,
        IXGBE_I2C_EEPROM_DEV_ADDR2,
    ) {
        Ok(data) => data,
        Err(e) => {
            log::debug!("Failed to read Rx Rate Select RS1\n");
            return Err(e);
        }
    };

    eeprom_data = (eeprom_data & !IXGBE_SFF_SOFT_RS_SELECT_MASK) | rs;

    if let Err(e) = ops.phy_write_i2c_byte(
        info,
        hw,
        IXGBE_SFF_SFF_8472_ESCB,
        IXGBE_I2C_EEPROM_DEV_ADDR2,
        eeprom_data,
    ) {
        log::debug!("Failed to write Rx Rate Select RS1\n");
        return Err(e);
    }

    Ok(())
}

/// setup_mac_link_multispeed_fiber - Set MAC link speed
/// Set the link speed in the MAC and/or PHY register and restarts link.
pub fn setup_mac_link_multispeed_fiber<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
    mut speed: u32,
    autoneg_wait_to_complete: bool,
) -> Result<(), IxgbeDriverErr> {
    fn out(
        hw: &mut IxgbeHw,
        speed: u32,
        status: Result<(), IxgbeDriverErr>,
    ) -> Result<(), IxgbeDriverErr> {
        hw.phy.autoneg_advertised = 0;
        if speed & IXGBE_LINK_SPEED_10GB_FULL != 0 {
            hw.phy.autoneg_advertised |= IXGBE_LINK_SPEED_10GB_FULL;
        }
        if speed & IXGBE_LINK_SPEED_1GB_FULL != 0 {
            hw.phy.autoneg_advertised |= IXGBE_LINK_SPEED_10GB_FULL;
        }
        status
    }

    use MediaType::*;

    // Mask off requested but non-supported speeds
    let (link_speed, _autoneg) = ops.mac_get_link_capabilities(info, hw)?;

    speed &= link_speed;

    //  Try each speed one by one, highest priority first.  We do this in
    // software because 10Gb fiber doesn't support speed autonegotiation.
    let mut speedcnt = 0;
    let mut highest_link_speed = IXGBE_LINK_SPEED_UNKNOWN;
    if speed & IXGBE_LINK_SPEED_10GB_FULL != 0 {
        speedcnt += 1;
        highest_link_speed = IXGBE_LINK_SPEED_10GB_FULL;

        // Set the module link speed
        match hw.phy.media_type {
            IxgbeMediaTypeFiberFixed | IxgbeMediaTypeFiber => {
                ops.mac_set_rate_select_speed(info, hw, IXGBE_LINK_SPEED_10GB_FULL)?;
            }
            IxgbeMediaTypeFiberQsfp => (), // QSFP module automatically detects MAC link speed
            _ => {
                log::debug!("Unexpected media type.\n");
            }
        }

        // Allow module to change analog characteristics (1G->10G)
        wait_millisec(40);

        ops.mac_setup_mac_link(
            info,
            hw,
            IXGBE_LINK_SPEED_10GB_FULL,
            autoneg_wait_to_complete,
        )?;

        // Flap the Tx laser if it has not already been done
        flap_tx_laser_multispeed_fiber(info, hw)?;

        // Wait for the controller to acquire link.  Per IEEE 802.3ap,
        // Section 73.10.2, we may have to wait up to 500ms if KR is
        // attempted.  82599 uses the same timing for 10g SFI.
        for _ in 0..5 {
            // Wait for the link partner to also set speed
            wait_millisec(100);

            // If we have link, just jump out
            let (link_speed, link_up) = ops.mac_check_link(info, hw, false)?;

            if link_up {
                return out(hw, link_speed, Ok(()));
            }
        }
    }

    if speed & IXGBE_LINK_SPEED_1GB_FULL != 0 {
        speedcnt += 1;
        if highest_link_speed == IXGBE_LINK_SPEED_UNKNOWN {
            highest_link_speed = IXGBE_LINK_SPEED_1GB_FULL;
        }

        // Set the module link speed
        match hw.phy.media_type {
            IxgbeMediaTypeFiberFixed | IxgbeMediaTypeFiber => {
                ops.mac_set_rate_select_speed(info, hw, IXGBE_LINK_SPEED_1GB_FULL)?;
            }
            IxgbeMediaTypeFiberQsfp => (), /* QSFP module automatically detects link speed */
            _ => {
                log::debug!("Unexpected media type.\n");
            }
        }

        // Allow module to change analog characteristics (10G->1G)
        wait_millisec(40);

        ops.mac_setup_mac_link(
            info,
            hw,
            IXGBE_LINK_SPEED_1GB_FULL,
            autoneg_wait_to_complete,
        )?;

        // Flap the Tx laser if it has not already been done
        if hw.mac.mac_type == MacType::IxgbeMac82599EB {
            flap_tx_laser_multispeed_fiber(info, hw)?;
        }

        // Wait for the link partner to also set speed
        wait_millisec(100);

        // If we have link, just jump out
        let (link_speed, link_up) = ops.mac_check_link(info, hw, false)?;

        if link_up {
            return out(hw, link_speed, Ok(()));
        }
    }

    // We didn't get link.  Configure back to the highest speed we tried,
    // (if there was more than one).  We call ourselves back with just the
    // single highest speed that the user requested.
    if speedcnt > 1 {
        let status = setup_mac_link_multispeed_fiber(
            ops,
            info,
            hw,
            highest_link_speed,
            autoneg_wait_to_complete,
        );
        return out(hw, speed, status);
    }

    out(hw, speed, Ok(()))
}

/// mng_enabled - Is the manageability engine enabled?
/// Returns TRUE if the manageability engine is enabled.
pub fn mng_enabled(info: &PCIeInfo, hw: &IxgbeHw) -> Result<bool, IxgbeDriverErr> {
    let fwsm = ixgbe_hw::read_reg(info, get_fwsm_offset(info.get_id())?)?;
    if (fwsm & IXGBE_FWSM_MODE_MASK) != IXGBE_FWSM_FW_MODE_PT {
        return Ok(false);
    }

    let manc = ixgbe_hw::read_reg(info, IXGBE_MANC)?;
    if manc & IXGBE_MANC_RCV_TCO_EN == 0 {
        return Ok(false);
    }

    if hw.mac.mac_type <= MacType::IxgbeMacX540 {
        let factps = ixgbe_hw::read_reg(info, get_factps_offset(info.get_id())?)?;
        if factps & IXGBE_FACTPS_MNGCG != 0 {
            return Ok(false);
        }
    }

    Ok(true)
}

/// probe_phy - Probe a single address for a PHY
/// Returns TRUE if PHY found
fn probe_phy<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
    phy_addr: u16,
) -> Result<(), IxgbeDriverErr> {
    use ixgbe_hw::PhyType::*;
    validate_phy_addr(ops, info, hw, phy_addr as u32)?;

    get_phy_id(ops, info, hw)?;

    hw.phy.phy_type = get_phy_type_from_id(hw.phy.id);

    if hw.phy.phy_type == IxgbePhyUnknown {
        let ext_ability = ops.phy_read_reg(
            info,
            hw,
            IXGBE_MDIO_PHY_EXT_ABILITY,
            IXGBE_MDIO_PMA_PMD_DEV_TYPE,
        )?;
        if (ext_ability as u32
            & (IXGBE_MDIO_PHY_10GBASET_ABILITY | IXGBE_MDIO_PHY_1000BASET_ABILITY))
            != 0
        {
            hw.phy.phy_type = IxgbePhyCuUnknown;
        } else {
            hw.phy.phy_type = IxgbePhyGeneric;
        }
    }

    Ok(())
}

/// validate_phy_addr - Determines phy address is valid
fn validate_phy_addr<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
    phy_addr: u32,
) -> Result<(), IxgbeDriverErr> {
    hw.phy.addr = phy_addr;
    let phy_id = ops.phy_read_reg(
        info,
        hw,
        IXGBE_MDIO_PHY_ID_HIGH,
        IXGBE_MDIO_PMA_PMD_DEV_TYPE,
    )?;

    if phy_id != 0xFFFF && phy_id != 0x0 {
        return Ok(());
    }

    Err(PhyAddrInvalid)
}

/// get_phy_id - Get the phy type
fn get_phy_id<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    let phy_id_high = ops.phy_read_reg(
        info,
        hw,
        IXGBE_MDIO_PHY_ID_HIGH,
        IXGBE_MDIO_PMA_PMD_DEV_TYPE,
    )?;

    hw.phy.id = (phy_id_high as u32) << 16;
    let phy_id_low =
        ops.phy_read_reg(info, hw, IXGBE_MDIO_PHY_ID_LOW, IXGBE_MDIO_PMA_PMD_DEV_TYPE)?;

    hw.phy.id |= phy_id_low as u32 & IXGBE_PHY_REVISION_MASK;
    hw.phy.revision = phy_id_low as u32 & !IXGBE_PHY_REVISION_MASK;
    Ok(())
}

/// get_phy_type_from_id - Get the phy type
fn get_phy_type_from_id(phy_id: u32) -> ixgbe_hw::PhyType {
    use ixgbe_hw::PhyType::*;

    match phy_id {
        TN1010_PHY_ID => IxgbePhyTn,
        X550_PHY_ID2 | X550_PHY_ID3 | X540_PHY_ID => IxgbePhyAq,
        QT2022_PHY_ID => IxgbePhyQt,
        ATH_PHY_ID => IxgbePhyNl,
        X557_PHY_ID | X557_PHY_ID2 => IxgbePhyX550emExtT,
        IXGBE_M88E1500_E_PHY_ID | IXGBE_M88E1543_E_PHY_ID => IxgbePhyExt1gT,
        _ => IxgbePhyUnknown,
    }
}

pub fn phy_identify_phy_generic<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    use ixgbe_hw::PhyType::*;

    if hw.phy.phy_semaphore_mask == 0 {
        if hw.bus.lan_id != 0 {
            hw.phy.phy_semaphore_mask = IXGBE_GSSR_PHY1_SM;
        } else {
            hw.phy.phy_semaphore_mask = IXGBE_GSSR_PHY0_SM;
        }
    }

    if hw.phy.phy_type != IxgbePhyUnknown {
        return Ok(());
    }

    let phy_addr;
    if hw.phy.nw_mng_if_sel != 0 {
        phy_addr = (hw.phy.nw_mng_if_sel & IXGBE_NW_MNG_IF_SEL_MDIO_PHY_ADD)
            >> IXGBE_NW_MNG_IF_SEL_MDIO_PHY_ADD_SHIFT;
        return probe_phy(ops, info, hw, phy_addr as u16);
    }

    let mut status = Err(PhyAddrInvalid);
    for phy_addr in 0..IXGBE_MAX_PHY_ADDR {
        match probe_phy(ops, info, hw, phy_addr) {
            Ok(()) => {
                status = Ok(());
                break;
            }
            Err(_) => {
                continue;
            }
        }
    }

    //  Certain media types do not have a phy so an address will not
    // be found and the code will take this path.  Caller has to
    // decide if it is an error or not.
    if status != Ok(()) {
        hw.phy.addr = 0;
    }

    status
}

/// phy_identify_module_generic - Identifies module type
/// Determines HW type and calls appropriate function.
pub fn phy_identify_module_generic<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    use MediaType::*;

    match ops.mac_get_media_type(info, hw) {
        IxgbeMediaTypeFiber => identify_sfp_module_generic(ops, info, hw),
        IxgbeMediaTypeFiberQsfp => identify_qsfp_module_generic(ops, info, hw),
        _ => {
            hw.phy.sfp_type = SfpType::IxgbeSfpTypeNotPresent;
            Err(IxgbeDriverErr::SfpNotPresent)
        }
    }
}

/// identify_sfp_module_generic - Identifies SFP modules
/// Searches for and identifies the SFP module and assigns appropriate PHY type.
fn identify_sfp_module_generic<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    fn handle_phy_read_i2c_eeprom_error(hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        hw.phy.sfp_type = SfpType::IxgbeSfpTypeNotPresent;
        if hw.phy.phy_type != PhyType::IxgbePhyNl {
            hw.phy.id = 0;
            hw.phy.phy_type = PhyType::IxgbePhyUnknown;
        }
        Err(IxgbeDriverErr::SfpNotPresent)
    }
    use MediaType::*;
    use PhyType::*;
    use SfpType::*;

    let stored_sfp_type = hw.phy.sfp_type;

    if ops.mac_get_media_type(info, hw) != IxgbeMediaTypeFiber {
        hw.phy.sfp_type = IxgbeSfpTypeNotPresent;
        return Err(IxgbeDriverErr::SfpNotPresent);
    }

    // LAN ID is needed for I2C access
    let (func, lan_id, instance_id) = ops.mac_set_lan_id(info, hw)?;
    hw.bus.func = func;
    hw.bus.lan_id = lan_id;
    hw.bus.instance_id = instance_id;

    let identifier = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_IDENTIFIER) {
        Ok(ret) => ret,
        Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
    };

    if identifier != IXGBE_SFF_IDENTIFIER_SFP {
        hw.phy.phy_type = IxgbePhySfpUnsupported;
        return Err(IxgbeDriverErr::SfpNotSupported);
    } else {
        let comp_codes_1g = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_1GBE_COMP_CODES) {
            Ok(ret) => ret,
            Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
        };

        let comp_codes_10g = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_10GBE_COMP_CODES) {
            Ok(ret) => ret,
            Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
        };

        let cable_tech = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_CABLE_TECHNOLOGY) {
            Ok(ret) => ret,
            Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
        };

        /* ID Module
         * =========
         * 0   SFP_DA_CU
         * 1   SFP_SR
         * 2   SFP_LR
         * 3   SFP_DA_CORE0 - 82599-specific
         * 4   SFP_DA_CORE1 - 82599-specific
         * 5   SFP_SR/LR_CORE0 - 82599-specific
         * 6   SFP_SR/LR_CORE1 - 82599-specific
         * 7   SFP_act_lmt_DA_CORE0 - 82599-specific
         * 8   SFP_act_lmt_DA_CORE1 - 82599-specific
         * 9   SFP_1g_cu_CORE0 - 82599-specific
         * 10  SFP_1g_cu_CORE1 - 82599-specific
         * 11  SFP_1g_sx_CORE0 - 82599-specific
         * 12  SFP_1g_sx_CORE1 - 82599-specific
         */
        #[allow(clippy::collapsible_else_if)]
        if hw.mac.mac_type == MacType::IxgbeMac82598EB {
            if cable_tech & IXGBE_SFF_DA_PASSIVE_CABLE != 0 {
                hw.phy.sfp_type = IxgbeSfpTypeDaCu;
            } else if comp_codes_10g & IXGBE_SFF_10GBASESR_CAPABLE != 0 {
                hw.phy.sfp_type = IxgbeSfpTypeSr;
            } else if comp_codes_10g & IXGBE_SFF_10GBASELR_CAPABLE != 0 {
                hw.phy.sfp_type = IxgbeSfpTypeLr;
            } else if comp_codes_10g & IXGBE_SFF_DA_BAD_HP_CABLE != 0 {
                hw.phy.sfp_type = IxgbeSfpTypeDaCu;
            } else {
                hw.phy.sfp_type = IxgbeSfpTypeUnknown;
            }
        } else {
            if cable_tech & IXGBE_SFF_DA_PASSIVE_CABLE != 0 {
                if hw.bus.lan_id == 0 {
                    hw.phy.sfp_type = IxgbeSfpTypeDaCuCore0;
                } else {
                    hw.phy.sfp_type = IxgbeSfpTypeDaCuCore1;
                }
            } else if cable_tech & IXGBE_SFF_DA_ACTIVE_CABLE != 0 {
                let cable_spec = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_CABLE_SPEC_COMP)
                {
                    Ok(ret) => ret,
                    Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
                };
                if cable_spec & IXGBE_SFF_DA_SPEC_ACTIVE_LIMITING != 0 {
                    if hw.bus.lan_id == 0 {
                        hw.phy.sfp_type = IxgbeSfpTypeDaActLmtCore0;
                    } else {
                        hw.phy.sfp_type = IxgbeSfpTypeDaActLmtCore1;
                    }
                } else {
                    hw.phy.sfp_type = IxgbeSfpTypeUnknown;
                }
            } else if comp_codes_10g & (IXGBE_SFF_10GBASESR_CAPABLE | IXGBE_SFF_10GBASELR_CAPABLE)
                != 0
            {
                if hw.bus.lan_id == 0 {
                    hw.phy.sfp_type = IxgbeSfpTypeSrlrCore0;
                } else {
                    hw.phy.sfp_type = IxgbeSfpTypeSrlrCore1;
                }
            } else if comp_codes_1g & IXGBE_SFF_1GBASET_CAPABLE != 0 {
                if hw.bus.lan_id == 0 {
                    hw.phy.sfp_type = IxgbeSfpType1gCuCore0;
                } else {
                    hw.phy.sfp_type = IxgbeSfpType1gCuCore1;
                }
            } else if comp_codes_1g & IXGBE_SFF_1GBASESX_CAPABLE != 0 {
                if hw.bus.lan_id == 0 {
                    hw.phy.sfp_type = IxgbeSfpType1gSxCore0;
                } else {
                    hw.phy.sfp_type = IxgbeSfpType1gSxCore1;
                }
            } else if comp_codes_1g & IXGBE_SFF_1GBASELX_CAPABLE != 0 {
                if hw.bus.lan_id == 0 {
                    hw.phy.sfp_type = IxgbeSfpType1gLxCore0;
                } else {
                    hw.phy.sfp_type = IxgbeSfpType1gLxCore1;
                }
            } else {
                hw.phy.sfp_type = IxgbeSfpTypeUnknown;
            }
        }

        if hw.phy.sfp_type != stored_sfp_type {
            hw.phy.sfp_setup_needed = true;
        }

        // Determine if the SFP+ PHY is dual speed or not.
        hw.phy.multispeed_fiber = false;
        if ((comp_codes_1g & IXGBE_SFF_1GBASESX_CAPABLE != 0)
            && (comp_codes_10g & IXGBE_SFF_10GBASESR_CAPABLE != 0))
            || ((comp_codes_1g & IXGBE_SFF_1GBASELX_CAPABLE != 0)
                && (comp_codes_10g & IXGBE_SFF_10GBASELR_CAPABLE != 0))
        {
            hw.phy.multispeed_fiber = true;
        }

        // Determine PHY vendor
        let mut oui_bytes = [0; 3];
        if hw.phy.phy_type != IxgbePhyNl {
            hw.phy.id = identifier as u32;
            oui_bytes[0] = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_VENDOR_OUI_BYTE0) {
                Ok(ret) => ret,
                Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
            };

            oui_bytes[1] = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_VENDOR_OUI_BYTE1) {
                Ok(ret) => ret,
                Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
            };

            oui_bytes[2] = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_VENDOR_OUI_BYTE2) {
                Ok(ret) => ret,
                Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
            };

            let vendor_oui = ((oui_bytes[0] as u32) << IXGBE_SFF_VENDOR_OUI_BYTE0_SHIFT)
                | ((oui_bytes[1] as u32) << IXGBE_SFF_VENDOR_OUI_BYTE1_SHIFT)
                | ((oui_bytes[2] as u32) << IXGBE_SFF_VENDOR_OUI_BYTE2_SHIFT);

            match vendor_oui {
                IXGBE_SFF_VENDOR_OUI_TYCO => {
                    if cable_tech & IXGBE_SFF_DA_PASSIVE_CABLE != 0 {
                        hw.phy.phy_type = IxgbePhySfpPassiveTyco;
                    }
                }
                IXGBE_SFF_VENDOR_OUI_FTL => {
                    if cable_tech & IXGBE_SFF_DA_ACTIVE_CABLE != 0 {
                        hw.phy.phy_type = IxgbePhySfpFtlActive;
                    } else {
                        hw.phy.phy_type = IxgbePhySfpFtl;
                    }
                }
                IXGBE_SFF_VENDOR_OUI_AVAGO => hw.phy.phy_type = IxgbePhySfpAvago,
                IXGBE_SFF_VENDOR_OUI_INTEL => hw.phy.phy_type = IxgbePhySfpIntel,
                _ => hw.phy.phy_type = IxgbePhySfpUnknown,
            }
        }

        // Allow any DA cable vendor
        if cable_tech & (IXGBE_SFF_DA_PASSIVE_CABLE | IXGBE_SFF_DA_ACTIVE_CABLE) != 0 {
            if cable_tech & IXGBE_SFF_DA_PASSIVE_CABLE != 0 {
                hw.phy.phy_type = IxgbePhySfpPassiveUnknown;
            } else if cable_tech & IXGBE_SFF_DA_ACTIVE_CABLE != 0 {
                hw.phy.phy_type = IxgbePhySfpActiveUnknown;
            }
            return Ok(());
        }

        // Verify supported 1G SFP modules
        match hw.phy.sfp_type {
            IxgbeSfpType1gCuCore0
            | IxgbeSfpType1gCuCore1
            | IxgbeSfpType1gLxCore0
            | IxgbeSfpType1gLxCore1
            | IxgbeSfpType1gSxCore0
            | IxgbeSfpType1gSxCore1 => (),
            _ => {
                if comp_codes_10g == 0 {
                    hw.phy.phy_type = IxgbePhySfpUnsupported;
                    return Err(IxgbeDriverErr::SfpNotSupported);
                }
            }
        }

        // We do not limit the definition of "supported SFP modules"
        // to the vendor/make whitelist.
    }

    Ok(())
}

/// identify_qsfp_module_generic - Identifies QSFP modules
/// Searches for and identifies the QSFP module and assigns appropriate PHY type
fn identify_qsfp_module_generic<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    use MediaType::*;
    use PhyType::*;
    use SfpType::*;
    fn handle_phy_read_i2c_eeprom_error(hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        hw.phy.sfp_type = SfpType::IxgbeSfpTypeNotPresent;
        hw.phy.id = 0;
        hw.phy.phy_type = PhyType::IxgbePhyUnknown;
        Err(IxgbeDriverErr::SfpNotPresent)
    }

    let stored_sfp_type = hw.phy.sfp_type;
    if ops.mac_get_media_type(info, hw) != IxgbeMediaTypeFiberQsfp {
        hw.phy.sfp_type = IxgbeSfpTypeNotPresent;
        return Err(IxgbeDriverErr::SfpNotPresent);
    }

    // LAN ID is needed for I2C access
    let (func, lan_id, instance_id) = ops.mac_set_lan_id(info, hw)?;
    hw.bus.func = func;
    hw.bus.lan_id = lan_id;
    hw.bus.instance_id = instance_id;

    let identifier = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_IDENTIFIER) {
        Ok(ret) => ret,
        Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
    };

    if identifier != IXGBE_SFF_IDENTIFIER_QSFP_PLUS {
        hw.phy.phy_type = IxgbePhySfpUnsupported;
        return Err(IxgbeDriverErr::SfpNotSupported);
    }

    hw.phy.id = identifier as u32;

    let comp_codes_10g = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_QSFP_10GBE_COMP) {
        Ok(ret) => ret,
        Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
    };

    let comp_codes_1g = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_QSFP_1GBE_COMP) {
        Ok(ret) => ret,
        Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
    };

    if comp_codes_10g & IXGBE_SFF_QSFP_DA_PASSIVE_CABLE != 0 {
        hw.phy.phy_type = IxgbePhyQsfpPassiveUnknown;
        if hw.bus.lan_id == 0 {
            hw.phy.sfp_type = IxgbeSfpTypeDaCuCore0;
        } else {
            hw.phy.sfp_type = IxgbeSfpTypeDaCuCore1;
        }
    } else if comp_codes_10g & (IXGBE_SFF_10GBASESR_CAPABLE | IXGBE_SFF_10GBASELR_CAPABLE) != 0 {
        if hw.bus.lan_id == 0 {
            hw.phy.sfp_type = IxgbeSfpTypeSrlrCore0;
        } else {
            hw.phy.sfp_type = IxgbeSfpTypeSrlrCore1;
        }
    } else {
        let mut active_cable = false;
        if comp_codes_10g & IXGBE_SFF_QSFP_DA_ACTIVE_CABLE != 0 {
            active_cable = true;
        }

        if !active_cable {
            // check for active DA cables that pre-date
            // SFF-8436 v3.6
            let connector = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_QSFP_CONNECTOR) {
                Ok(ret) => ret,
                Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
            };

            let cable_length = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_QSFP_CABLE_LENGTH)
            {
                Ok(ret) => ret,
                Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
            };

            let device_tech = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_QSFP_DEVICE_TECH) {
                Ok(ret) => ret,
                Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
            };
            if (connector == IXGBE_SFF_QSFP_CONNECTOR_NOT_SEPARABLE)
                && (cable_length > 0)
                && ((device_tech >> 4) == IXGBE_SFF_QSFP_TRANSMITER_850NM_VCSEL)
            {
                active_cable = true;
            }
        }

        if active_cable {
            hw.phy.phy_type = IxgbePhyQsfpActiveUnknown;
            if hw.bus.lan_id == 0 {
                hw.phy.sfp_type = IxgbeSfpTypeDaActLmtCore0;
            } else {
                hw.phy.sfp_type = IxgbeSfpTypeDaActLmtCore1;
            }
        } else {
            // unsupported module type
            hw.phy.phy_type = IxgbePhySfpUnsupported;
            return Err(SfpNotSupported);
        }
    }

    if hw.phy.sfp_type != stored_sfp_type {
        hw.phy.sfp_setup_needed = true;
    }

    // Determine if the QSFP+ PHY is dual speed or not.
    hw.phy.multispeed_fiber = false;
    if ((comp_codes_1g & IXGBE_SFF_1GBASESX_CAPABLE != 0)
        && (comp_codes_10g & IXGBE_SFF_10GBASESR_CAPABLE != 0))
        || ((comp_codes_1g & IXGBE_SFF_1GBASELX_CAPABLE != 0)
            && (comp_codes_10g & IXGBE_SFF_10GBASELR_CAPABLE != 0))
    {
        hw.phy.multispeed_fiber = true;
    }

    // Determine PHY vendor for optical modules
    let mut oui_bytes = [0; 3];
    if comp_codes_10g & (IXGBE_SFF_10GBASESR_CAPABLE | IXGBE_SFF_10GBASELR_CAPABLE) != 0 {
        oui_bytes[0] = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_QSFP_VENDOR_OUI_BYTE0) {
            Ok(ret) => ret,
            Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
        };

        oui_bytes[1] = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_QSFP_VENDOR_OUI_BYTE1) {
            Ok(ret) => ret,
            Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
        };

        oui_bytes[2] = match ops.phy_read_i2c_eeprom(info, hw, IXGBE_SFF_QSFP_VENDOR_OUI_BYTE2) {
            Ok(ret) => ret,
            Err(_) => return handle_phy_read_i2c_eeprom_error(hw),
        };

        let vendor_oui = ((oui_bytes[0] as u32) << IXGBE_SFF_VENDOR_OUI_BYTE0_SHIFT)
            | ((oui_bytes[1] as u32) << IXGBE_SFF_VENDOR_OUI_BYTE1_SHIFT)
            | ((oui_bytes[2] as u32) << IXGBE_SFF_VENDOR_OUI_BYTE2_SHIFT);

        if vendor_oui == IXGBE_SFF_VENDOR_OUI_INTEL {
            hw.phy.phy_type = IxgbePhyQsfpIntel;
        } else {
            hw.phy.phy_type = IxgbePhyQsfpUnknown;
        }

        // We do not limit the definition of "supported QSFP modules"
        // to the vendor/make whitelist.
    }
    Ok(())
}

/// i2c_bus_clear - Clears the I2C bus
/// Clears the I2C bus by sending nine clock pulses.
/// Used when data line is stuck low.
fn i2c_bus_clear(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let i2cctl_offset = get_i2cctl_offset(info.get_id())?;

    i2c_start(info)?;
    let mut i2cctl = ixgbe_hw::read_reg(info, i2cctl_offset)?;

    i2cctl = set_i2c_data(info, i2cctl, true)?;

    for _ in 0..9 {
        i2cctl = raise_i2c_clk(info, i2cctl)?;

        // Min high period of clock is 4us
        wait_microsec(IXGBE_I2C_T_HIGH);

        i2cctl = lower_i2c_clk(info, i2cctl)?;

        // Min low period of clock is 4.7us
        wait_microsec(IXGBE_I2C_T_LOW);
    }

    i2c_start(info)?;

    // Put the i2c bus back to default state
    i2c_stop(info)?;

    Ok(())
}

/// read_i2c_byte_generic_int - Reads 8 bit word over I2C
/// Performs byte read operation to SFP module's EEPROM over I2C interface at
/// a specified device address.
pub fn read_i2c_byte_generic_int<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &IxgbeHw,
    byte_offset: u8,
    dev_addr: u8,
    lock: bool,
) -> Result<u8, IxgbeDriverErr> {
    let mut max_retry = 10;
    if hw.mac.mac_type >= MacType::IxgbeMacX550 {
        max_retry = 3;
    }
    if is_sfp_probe(hw, byte_offset, dev_addr) {
        max_retry = IXGBE_SFP_DETECT_RETRIES;
    }

    let swfw_mask = hw.phy.phy_semaphore_mask;

    let body = || {
        i2c_start(info)?;

        // Device Address and write indication
        clock_out_i2c_byte(info, dev_addr)?;
        get_i2c_ack(info)?;
        clock_out_i2c_byte(info, byte_offset)?;
        get_i2c_ack(info)?;
        i2c_start(info)?;

        // Device Address and read indication
        clock_out_i2c_byte(info, dev_addr | 0x1)?;
        get_i2c_ack(info)?;
        let result = clock_in_i2c_byte(info)?;
        clock_out_i2c_bit(info, true)?;
        i2c_stop(info)?;

        if lock {
            ops.mac_release_swfw_sync(info, swfw_mask)?;
        }

        Ok::<u8, IxgbeDriverErr>(result)
    };

    let mut err = Err(IxgbeDriverErr::I2c);
    for _ in 0..max_retry {
        if lock {
            ops.mac_acquire_swfw_sync(info, swfw_mask)?;
        }

        match body() {
            Ok(ret) => return Ok(ret),
            Err(e) => {
                i2c_bus_clear(info)?;
                if lock {
                    ops.mac_release_swfw_sync(info, swfw_mask)?;
                    wait_millisec(100);
                }

                err = Err(e);

                log::debug!("I2C byte read error - Retrying.\n");
            }
        }
    }

    log::debug!("I2C byte read error.\n");

    err
}

/// write_i2c_byte_generic_int - Writes 8 bit word over I2C
/// Performs byte write operation to SFP module's EEPROM over I2C interface at
/// a specified device address.
pub fn write_i2c_byte_generic_int<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &IxgbeHw,
    byte_offset: u8,
    dev_addr: u8,
    data: u8,
    lock: bool,
) -> Result<(), IxgbeDriverErr> {
    let swfw_mask = hw.phy.phy_semaphore_mask;
    let max_retry = 1;

    if lock {
        ops.mac_acquire_swfw_sync(info, swfw_mask)?;
    }

    let body = || {
        i2c_start(info)?;

        clock_out_i2c_byte(info, dev_addr)?;
        get_i2c_ack(info)?;
        clock_out_i2c_byte(info, byte_offset)?;
        get_i2c_ack(info)?;
        clock_out_i2c_byte(info, data)?;
        get_i2c_ack(info)?;
        i2c_stop(info)?;

        if lock {
            ops.mac_release_swfw_sync(info, swfw_mask)?;
        }

        Ok::<(), IxgbeDriverErr>(())
    };

    let mut err = Err(IxgbeDriverErr::I2c);
    for _ in 0..max_retry {
        match body() {
            Ok(_) => return Ok(()),
            Err(e) => {
                i2c_bus_clear(info)?;

                if lock {
                    ops.mac_release_swfw_sync(info, swfw_mask)?;
                }

                err = Err(e)
            }
        }
    }

    err
}

/// is_sfp_probe - Returns TRUE if SFP is being detected
fn is_sfp_probe(hw: &IxgbeHw, offset: u8, addr: u8) -> bool {
    use SfpType::*;

    if addr == IXGBE_I2C_EEPROM_DEV_ADDR
        && offset == IXGBE_SFF_IDENTIFIER
        && hw.phy.sfp_type == IxgbeSfpTypeNotPresent
    {
        return true;
    }
    false
}

/// i2c_start - Sets I2C start condition
/// Sets I2C start condition (High -> Low on SDA while SCL is High)
/// Set bit-bang mode on X550 hardware.
fn i2c_start(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let i2cctl_offset = get_i2cctl_offset(info.get_id())?;
    let mut i2cctl = ixgbe_hw::read_reg(info, i2cctl_offset)?;
    let bb_en_bit = get_i2c_bb_en_offset(info.get_id())?;

    i2cctl |= bb_en_bit as u32;

    // Start condition must begin with data and clock high
    i2cctl = set_i2c_data(info, i2cctl, true)?;
    i2cctl = raise_i2c_clk(info, i2cctl)?;

    // Setup time for start condition (4.7us)
    wait_microsec(IXGBE_I2C_T_SU_STA);

    i2cctl = set_i2c_data(info, i2cctl, false)?;

    // Hold time for start condition (4us)
    wait_microsec(IXGBE_I2C_T_HD_STA);

    _ = lower_i2c_clk(info, i2cctl)?;

    // Minimum low period of clock is 4.7 us
    wait_microsec(IXGBE_I2C_T_LOW);

    Ok(())
}

/// i2c_stop - Sets I2C stop condition
/// Sets I2C stop condition (Low -> High on SDA while SCL is High)
/// Disables bit-bang mode and negates data output enable on X550
/// hardware.
fn i2c_stop(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let clk_oe_bit = get_i2c_clk_oe_n_en_offset(info.get_id())?;
    let bb_en_bit = get_i2c_bb_en_offset(info.get_id())?;
    let i2cctl_offset = get_i2cctl_offset(info.get_id())?;
    let mut i2cctl = ixgbe_hw::read_reg(info, i2cctl_offset)?;
    let data_oe_bit = get_i2c_data_oe_n_en_offset(info.get_id())?;

    // Stop condition must begin with data low and clock high
    i2cctl = set_i2c_data(info, i2cctl, false)?;
    i2cctl = raise_i2c_clk(info, i2cctl)?;

    // Setup time for stop condition (4us)
    wait_microsec(IXGBE_I2C_T_SU_STO);

    i2cctl = set_i2c_data(info, i2cctl, true)?;

    // bus free time between stop and start (4.7us)
    wait_microsec(IXGBE_I2C_T_BUF);

    if (bb_en_bit != 0) || (data_oe_bit != 0) || (clk_oe_bit != 0) {
        i2cctl &= !bb_en_bit as u32;
        i2cctl |= (data_oe_bit | clk_oe_bit) as u32;
        ixgbe_hw::write_reg(info, i2cctl_offset, i2cctl)?;
        ixgbe_hw::write_flush(info)?;
    }

    Ok(())
}

/// clock_in_i2c_byte - Clocks in one byte via I2C
/// Clocks in one byte data via I2C data/clock
fn clock_in_i2c_byte(info: &PCIeInfo) -> Result<u8, IxgbeDriverErr> {
    let mut data = 0;
    for i in (0..=7).rev() {
        let bit_bool = clock_in_i2c_bit(info)?;
        data |= (bit_bool as u8) << i;
    }

    Ok(data)
}

/// clock_out_i2c_byte - Clocks out one byte via I2C
/// Clocks out one byte data via I2C data/clock
fn clock_out_i2c_byte(info: &PCIeInfo, data: u8) -> Result<(), IxgbeDriverErr> {
    let i2cctl_offset = get_i2cctl_offset(info.get_id())?;
    let data_oe_bit = get_i2c_data_oe_n_en_offset(info.get_id())?;
    let data_out_offset = get_i2c_data_out_offset(info.get_id())?;

    let mut status = Ok(());
    for i in (0..=7).rev() {
        let bit = (data >> i) & 0x1;
        if let Err(e) = clock_out_i2c_bit(info, bit == 1) {
            status = Err(e);
            break;
        }
    }

    // Release SDA line (set high)
    let mut i2cctl = ixgbe_hw::read_reg(info, i2cctl_offset)?;
    i2cctl |= data_out_offset as u32;
    i2cctl |= data_oe_bit as u32;
    ixgbe_hw::write_reg(info, i2cctl_offset, i2cctl)?;
    ixgbe_hw::write_flush(info)?;

    status
}

/// get_i2c_ack - Polls for I2C ACK
/// Clocks in/out one bit via I2C data/clock
fn get_i2c_ack(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let i2cctl_offset = get_i2cctl_offset(info.get_id())?;
    let mut i2cctl = ixgbe_hw::read_reg(info, i2cctl_offset)?;
    let data_oe_bit = get_i2c_data_oe_n_en_offset(info.get_id())?;
    let data_out_offset = get_i2c_data_out_offset(info.get_id())?;

    if data_oe_bit != 0 {
        i2cctl |= data_out_offset as u32;
        i2cctl |= data_oe_bit as u32;
        ixgbe_hw::write_reg(info, i2cctl_offset, i2cctl)?;
        ixgbe_hw::write_flush(info)?;
    }
    i2cctl = raise_i2c_clk(info, i2cctl)?;

    // Minimum high period of clock is 4us
    wait_microsec(IXGBE_I2C_T_HIGH);

    //  Poll for ACK.  Note that ACK in I2C spec is
    // transition from 1 to 0
    let timeout = 10;
    let mut ack = true;
    for _ in 0..timeout {
        i2cctl = ixgbe_hw::read_reg(info, i2cctl_offset)?;
        (ack, i2cctl) = get_i2c_data(info, i2cctl)?;

        wait_microsec(1);
        if !ack {
            break;
        }
    }

    let mut status = Ok(());
    if ack {
        log::debug!("I2C ack was not received.\n");
        status = Err(IxgbeDriverErr::I2c);
    }

    _ = lower_i2c_clk(info, i2cctl)?;

    // Minimum low period of clock is 4.7 us
    wait_microsec(IXGBE_I2C_T_LOW);

    status
}

/// clock_in_i2c_bit - Clocks in one bit via I2C data/clock
/// Clocks in one bit via I2C data/clock
fn clock_in_i2c_bit(info: &PCIeInfo) -> Result<bool, IxgbeDriverErr> {
    let i2cctl_offset = get_i2cctl_offset(info.get_id())?;
    let mut i2cctl = ixgbe_hw::read_reg(info, i2cctl_offset)?;
    let data_oe_bit = get_i2c_data_oe_n_en_offset(info.get_id())?;
    let data_out_offset = get_i2c_data_out_offset(info.get_id())?;

    if data_oe_bit != 0 {
        i2cctl |= data_out_offset as u32;
        i2cctl |= data_oe_bit as u32;
        ixgbe_hw::write_reg(info, i2cctl_offset, i2cctl)?;
        ixgbe_hw::write_flush(info)?;
    }
    _ = raise_i2c_clk(info, i2cctl)?;

    // Minimum high period of clock is 4us
    wait_microsec(IXGBE_I2C_T_HIGH);

    i2cctl = ixgbe_hw::read_reg(info, i2cctl_offset)?;
    let (data, new_i2cctl) = get_i2c_data(info, i2cctl)?;

    _ = lower_i2c_clk(info, new_i2cctl)?;

    // Minimum low period of clock is 4.7 us
    wait_microsec(IXGBE_I2C_T_LOW);

    Ok(data)
}

/// clock_out_i2c_bit - Clocks in/out one bit via I2C data/clock
/// Clocks out one bit via I2C data/clock
fn clock_out_i2c_bit(info: &PCIeInfo, data: bool) -> Result<(), IxgbeDriverErr> {
    let i2cctl_offset = get_i2cctl_offset(info.get_id())?;
    let i2cctl = ixgbe_hw::read_reg(info, i2cctl_offset)?;

    match set_i2c_data(info, i2cctl, data) {
        Ok(i2cctl) => {
            let new_i2cctl = raise_i2c_clk(info, i2cctl)?;

            // Minimum high period of clock is 4us
            wait_microsec(IXGBE_I2C_T_HIGH);

            _ = lower_i2c_clk(info, new_i2cctl)?;

            // Minimum low period of clock is 4.7 us.
            // This also takes care of the data hold time.
            wait_microsec(IXGBE_I2C_T_LOW);

            Ok(())
        }
        Err(_) => {
            log::error!("I2C data was not set to {}\n", data);
            Err(IxgbeDriverErr::I2c)
        }
    }
}

/// raise_i2c_clk - Raises the I2C SCL clock
/// Raises the I2C clock line '0'->'1'
/// Negates the I2C clock output enable on X550 hardware.
fn raise_i2c_clk(info: &PCIeInfo, mut i2cctl: u32) -> Result<u32, IxgbeDriverErr> {
    let i2c_clk_in_offset = get_i2c_clk_in_offset(info.get_id())?;
    let i2c_clk_out_offset = get_i2c_clk_out_offset(info.get_id())?;
    let i2c_clk_oe_n_en_offset = get_i2c_clk_oe_n_en_offset(info.get_id())?;
    let i2cctl_offset = get_i2cctl_offset(info.get_id())?;

    if i2c_clk_oe_n_en_offset != 0 {
        i2cctl |= i2c_clk_oe_n_en_offset as u32;
        ixgbe_hw::write_reg(info, i2cctl_offset, i2cctl)?;
    }

    let timeout = IXGBE_I2C_CLOCK_STRETCHING_TIMEOUT;
    for _ in 0..timeout {
        i2cctl |= i2c_clk_out_offset as u32;

        ixgbe_hw::write_reg(info, i2cctl_offset, i2cctl)?;
        ixgbe_hw::write_flush(info)?;
        // SCL rise time (1000ns)
        wait_microsec(IXGBE_I2C_T_RISE);

        let i2cctl_r = ixgbe_hw::read_reg(info, i2cctl_offset)?;
        if i2cctl_r & i2c_clk_in_offset as u32 != 0 {
            break;
        }
    }

    Ok(i2cctl)
}

/// lower_i2c_clk - Lowers the I2C SCL clock
/// Lowers the I2C clock line '1'->'0'
/// Asserts the I2C clock output enable on X550 hardware.
fn lower_i2c_clk(info: &PCIeInfo, mut i2cctl: u32) -> Result<u32, IxgbeDriverErr> {
    let i2c_clk_out_offset = get_i2c_clk_out_offset(info.get_id())?;
    let i2c_clk_oe_n_en_offset = get_i2c_clk_oe_n_en_offset(info.get_id())?;
    let i2cctl_offset = get_i2cctl_offset(info.get_id())?;

    i2cctl &= !i2c_clk_out_offset as u32;
    i2cctl &= !i2c_clk_oe_n_en_offset as u32;

    ixgbe_hw::write_reg(info, i2cctl_offset, i2cctl)?;
    ixgbe_hw::write_flush(info)?;

    // SCL fall time (300ns)
    wait_microsec(IXGBE_I2C_T_FALL);

    Ok(i2cctl)
}

/// set_i2c_data - Sets the I2C data bit
/// Sets the I2C data bit
/// Asserts the I2C data output enable on X550 hardware.
fn set_i2c_data(info: &PCIeInfo, mut i2cctl: u32, data: bool) -> Result<u32, IxgbeDriverErr> {
    let data_oe_bit = get_i2c_data_oe_n_en_offset(info.get_id())?;
    let i2cctl_offset = get_i2cctl_offset(info.get_id())?;
    let i2c_data_out_offset = get_i2c_data_out_offset(info.get_id())?;

    if data {
        i2cctl |= i2c_data_out_offset as u32;
    } else {
        i2cctl &= !i2c_data_out_offset as u32;
    }
    i2cctl &= !data_oe_bit as u32;

    ixgbe_hw::write_reg(info, i2cctl_offset, i2cctl)?;
    ixgbe_hw::write_flush(info)?;

    // Data rise/fall (1000ns/300ns) and set-up time (250ns)
    wait_microsec(IXGBE_I2C_T_RISE + IXGBE_I2C_T_FALL + IXGBE_I2C_T_SU_DATA);

    if !data {
        // Can't verify data in this case
        return Ok(i2cctl);
    }
    if data_oe_bit != 0 {
        i2cctl |= data_oe_bit as u32;
        ixgbe_hw::write_reg(info, i2cctl_offset, i2cctl)?;
        ixgbe_hw::write_flush(info)?;
    }

    // Verify data was set correctly
    i2cctl = ixgbe_hw::read_reg(info, i2cctl_offset)?;
    match get_i2c_data(info, i2cctl)? {
        (true, new_i2cctl) => Ok(new_i2cctl),
        (false, _new_i2cctl) => {
            log::error!("Error - I2C data was not set to {}.\n", data);
            Err(IxgbeDriverErr::I2c)
        }
    }
}

/// get_i2c_data - Reads the I2C SDA data bit
/// Returns the I2C data bit value
/// Negates the I2C data output enable on X550 hardware.
fn get_i2c_data(info: &PCIeInfo, mut i2cctl: u32) -> Result<(bool, u32), IxgbeDriverErr> {
    let data_oe_bit = get_i2c_data_oe_n_en_offset(info.get_id())?;
    let i2cctl_offset = get_i2cctl_offset(info.get_id())?;
    let i2c_data_in_offset = get_i2c_data_in_offset(info.get_id())?;

    if data_oe_bit != 0 {
        i2cctl |= data_oe_bit as u32;
        ixgbe_hw::write_reg(info, i2cctl_offset, i2cctl)?;
        ixgbe_hw::write_flush(info)?;
        wait_microsec(IXGBE_I2C_T_FALL);
    }
    let data = (i2cctl & i2c_data_in_offset as u32) != 0;

    Ok((data, i2cctl))
}

/// check_reset_blocked - check status of MNG FW veto bit
/// This function checks the MMNGC.MNG_VETO bit to see if there are
/// any constraints on link from manageability.  For MAC's that don't
/// have this bit just return faluse since the link can not be blocked
/// via this method.
pub fn check_reset_blocked(info: &PCIeInfo, hw: &IxgbeHw) -> Result<bool, IxgbeDriverErr> {
    // If we don't have this bit, it can't be blocking
    if hw.mac.mac_type == MacType::IxgbeMac82598EB {
        return Ok(false);
    }

    let mmngc = ixgbe_hw::read_reg(info, IXGBE_MMNGC)?;
    if mmngc & IXGBE_MMNGC_MNG_VETO != 0 {
        log::error!("MNG_VETO bit detected.\n");
        return Ok(true);
    }

    Ok(false)
}

/// Eeprom Helper Functions
fn poll_eerd_eewr_done(info: &PCIeInfo, ee_reg: u32) -> Result<(), IxgbeDriverErr> {
    let mut reg;

    for _ in 0..IXGBE_EERD_EEWR_ATTEMPTS {
        if ee_reg == IXGBE_NVM_POLL_READ as u32 {
            reg = ixgbe_hw::read_reg(info, IXGBE_EERD)?;
        } else {
            reg = ixgbe_hw::read_reg(info, IXGBE_EEWR)?;
        }
        if reg & IXGBE_EEPROM_RW_REG_DONE as u32 != 0 {
            return Ok(());
        }
        wait_microsec(5);
    }

    log::error!("EEPROM read/write done polling timed out");
    Err(Eeprom)
}

pub fn read_eerd_buffer_generic<T: IxgbeOperations + ?Sized>(
    ops: &T, // &dyn IxgbeOperations,
    info: &PCIeInfo,
    eeprom: &mut IxgbeEepromInfo,
    offset: u16,
    words: u16,
    data: &mut [u16],
) -> Result<(), IxgbeDriverErr> {
    let mut eerd;

    if eeprom.eeprom_type == EepromType::IxgbeEepromUninitialized {
        ops.eeprom_init_params(info, eeprom)?;
    }

    if words == 0 {
        log::error!("Invalid EEPROM words");
        return Err(IxgbeDriverErr::InvalidArgument);
    }

    if words as usize != data.len() {
        log::error!("EEPROM words doesn't match the size of the buffer");
        return Err(IxgbeDriverErr::InvalidArgument);
    }

    if offset >= eeprom.word_size {
        log::error!("Invalid EEPROM offset");
        return Err(IxgbeDriverErr::Eeprom);
    }

    for (i, d) in data.iter_mut().enumerate() {
        eerd = ((offset + i as u16) << IXGBE_EEPROM_RW_ADDR_SHIFT) | IXGBE_EEPROM_RW_REG_START;

        ixgbe_hw::write_reg(info, IXGBE_EERD, eerd as u32)?;
        poll_eerd_eewr_done(info, IXGBE_NVM_POLL_READ as u32)?;
        *d = (ixgbe_hw::read_reg(info, IXGBE_EERD)? >> IXGBE_EEPROM_RW_REG_DATA) as u16;
    }

    Ok(())
}

fn check_address_cycle_complete(info: &PCIeInfo) -> Result<u32, IxgbeDriverErr> {
    let mut command = 0;
    for _i in 0..IXGBE_MDIO_COMMAND_TIMEOUT {
        wait_microsec(10);

        command = ixgbe_hw::read_reg(info, IXGBE_MSCA)?;
        if (command & IXGBE_MSCA_MDI_COMMAND as u32) == 0 {
            return Ok(command);
        }
    }

    Ok(command)
}

/// hic_unlocked - Issue command to manageability block unlocked
///  Communicates with the manageability block. On success return IXGBE_SUCCESS
/// else returns semaphore error when encountering an error acquiring
/// semaphore or IXGBE_ERR_HOST_INTERFACE_COMMAND when command fails.
/// This function assumes that the IXGBE_GSSR_SW_MNG_SM semaphore is held
/// by the caller.
pub fn hic_unlocked(
    info: &PCIeInfo,
    buffer: &[u32],
    length: u32,
    timeout: u32,
) -> Result<(), IxgbeDriverErr> {
    if (length == 0) || (length > IXGBE_HI_MAX_BLOCK_BYTE_LENGTH) {
        log::debug!("Buffer length failure buffersize={}.", length);
        return Err(IxgbeDriverErr::HostInterfaceCommand);
    }

    // Set bit 9 of FWSTS clearing FW reset indication
    let fwsts = ixgbe_hw::read_reg(info, IXGBE_FWSTS)?;
    ixgbe_hw::write_reg(info, IXGBE_FWSTS, fwsts | IXGBE_FWSTS_FWRI)?;

    // Check that the host interface is enabled.
    let mut hicr = ixgbe_hw::read_reg(info, IXGBE_HICR)?;
    if (hicr & IXGBE_HICR_EN) == 0 {
        log::debug!("IXGBE_HOST_EN bit disabled.\n");
        return Err(IxgbeDriverErr::HostInterfaceCommand);
    }

    // Calculate length in DWORDs. We must be DWORD aligned
    if length % (core::mem::size_of::<u32>() as u32) != 0 {
        log::debug!("Buffer length failure, not aligned to dword");
        return Err(InvalidArgument);
    }

    let dword_len = (length >> 2) as usize;

    // The device driver writes the relevant command block
    // into the ram area.
    //for i in 0..dword_len {
    for (i, item) in buffer.iter().enumerate().take(dword_len) {
        ixgbe_hw::write_reg_array(info, IXGBE_FLEX_MNG, i, u32::to_le(*item))?;
    }

    // Setting this bit tells the ARC that a new command is pending.
    ixgbe_hw::write_reg(info, IXGBE_HICR, hicr | IXGBE_HICR_C)?;

    let mut ended_by_break = false;
    for _ in 0..timeout {
        hicr = ixgbe_hw::read_reg(info, IXGBE_HICR)?;
        if hicr & IXGBE_HICR_C == 0 {
            ended_by_break = true;
            break;
        }
        wait_millisec(1);
    }

    // Check command completion
    if (timeout != 0 && !ended_by_break)
        || (ixgbe_hw::read_reg(info, IXGBE_HICR)? & IXGBE_HICR_SV) == 0
    {
        log::error!("Command has failed with no status valid.");
        return Err(HostInterfaceCommand);
    }

    Ok(())
}

/// host_interface_command - Issue command to manageability block
/// Needed because FW structures are big endian and decoding of
/// these fields can be 8 bit or 16 bit based on command. Decoding
/// is not easily understood without making a table of commands.
/// So we will leave this up to the caller to read back the data
/// in these cases.
/// Communicates with the manageability block. On success return IXGBE_SUCCESS
/// else returns semaphore error when encountering an error acquiring
/// semaphore or IXGBE_ERR_HOST_INTERFACE_COMMAND when command fails.
pub fn host_interface_command<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    buffer: &[u32],
    length: u32,
    timeout: u32,
    return_data: bool,
) -> Result<Option<[u32; 4]>, IxgbeDriverErr> {
    log::debug!("ixgbe: host_interface_command");

    if length == 0 || length > IXGBE_HI_MAX_BLOCK_BYTE_LENGTH {
        log::debug!("ixgbe: Buffer length failure buffersize={}.\n", length);
        return Err(IxgbeDriverErr::HostInterfaceCommand);
    }

    mac_swfw_sync_mut(ops, info, IXGBE_GSSR_SW_MNG_SM, 0, || {
        hic_unlocked(info, buffer, length, timeout)?;

        if !return_data {
            return Ok(None);
        }

        let mut hdr_size = core::mem::size_of::<IxgbeHicHdr>();
        // Calculate length in DWORDs
        let mut dword_len = hdr_size >> 2;

        let mut ret_buffer = [0; 4];
        // first pull in the header so we know the buffer length
        let mut bi = 0;
        while bi < dword_len {
            ret_buffer[bi] = u32::from_le(ixgbe_hw::read_reg_array(info, IXGBE_FLEX_MNG, bi)?);
            bi += 1;
        }

        let resp = unsafe { core::mem::transmute_copy::<_, IxgbeHicHdr>(&ret_buffer) };

        // If there is any thing in data position pull it in
        // Read Flash command requires reading buffer length from
        // two byes instead of one byte
        let buf_len;

        if resp.cmd == 0x30 {
            while bi < dword_len + 2 {
                ret_buffer[bi] = u32::from_le(ixgbe_hw::read_reg_array(info, IXGBE_FLEX_MNG, bi)?);
                bi += 1;
            }
            buf_len = (((resp.cmd_or_resp as u16) << 3) & 0xF00) | (resp.buf_len as u16);
            hdr_size += 2 << 2;
        } else {
            buf_len = resp.buf_len as u16;
        }
        if buf_len == 0 {
            return Ok(None);
        }

        if (length as usize) < buf_len as usize + hdr_size {
            log::debug!("Buffer not large enough for reply message.\n");
            return Err(HostInterfaceCommand);
        }

        // Calculate length in DWORDs, add 3 for odd lengths
        dword_len = (buf_len as usize + 3) >> 2;

        // Pull in the rest of the buffer (bi is where we left off)
        while bi < dword_len {
            ret_buffer[bi] = u32::from_le(ixgbe_hw::read_reg_array(info, IXGBE_FLEX_MNG, bi)?);
            bi += 1;
        }

        Ok(Some(ret_buffer))
    })
}

pub fn mac_swfw_sync_mut<T, F, W>(
    ops: &T,
    info: &PCIeInfo,
    mask: u32,
    semaphore_delay: u32,
    mut f: F,
) -> Result<W, IxgbeDriverErr>
where
    T: IxgbeOperations + ?Sized,
    F: FnMut() -> Result<W, IxgbeDriverErr>,
{
    ops.mac_acquire_swfw_sync(info, mask)?;
    let result = f();
    ops.mac_release_swfw_sync(info, mask)?;
    wait_millisec(semaphore_delay as u64);
    result
}

fn acquire_eeprom<T, F, W>(
    ops: &T,
    info: &PCIeInfo,
    eeprom: &IxgbeEepromInfo,
    mut f: F,
) -> Result<W, IxgbeDriverErr>
where
    T: IxgbeOperations + ?Sized,
    F: FnMut(&T) -> Result<W, IxgbeDriverErr>,
{
    log::debug!("ixgbe_acquire_eeprom");

    mac_swfw_sync_mut(ops, info, IXGBE_GSSR_EEP_SM, eeprom.semaphore_delay, || {
        let eec_offset = get_eec_offset(info.get_id())?;

        let mut eec = ixgbe_hw::read_reg(info, eec_offset)?;

        // Request EEPROM Access
        eec |= IXGBE_EEC_REQ;
        ixgbe_hw::write_reg(info, eec_offset, eec)?;

        for _ in 0..IXGBE_EEPROM_GRANT_ATTEMPTS {
            eec = ixgbe_hw::read_reg(info, eec_offset)?;
            if eec & IXGBE_EEC_GNT != 0 {
                break;
            }
            wait_microsec(5);
        }

        // Release if grant not acquired
        if eec & IXGBE_EEC_GNT == 0 {
            eec &= !IXGBE_EEC_REQ;
            ixgbe_hw::write_reg(info, eec_offset, eec)?;
            log::debug!("Could not acquire EEPROM grant\n");
            return Err(IxgbeDriverErr::Eeprom);
        }

        // Setup EEPROM for Read/Write
        // Clear CS and SK
        eec &= !(IXGBE_EEC_CS | IXGBE_EEC_SK);
        ixgbe_hw::write_reg(info, eec_offset, eec)?;
        ixgbe_hw::write_flush(info)?;
        wait_microsec(1);

        let result = f(ops);

        let mut eec = ixgbe_hw::read_reg(info, eec_offset)?;

        eec |= IXGBE_EEC_CS; // Pull CS high
        eec &= !IXGBE_EEC_SK; // Lower SCK

        ixgbe_hw::write_reg(info, eec_offset, eec)?;
        ixgbe_hw::write_flush(info)?;

        wait_microsec(1);

        // Stop requesting EEPROM access
        eec &= !IXGBE_EEC_REQ;
        ixgbe_hw::write_reg(info, eec_offset, eec)?;

        result
    })
}

/// Sets the hardware semaphores so EEPROM access can occur for bit-bang method
fn get_eeprom_semaphore(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let timeout: u32 = 2000;
    let mut swsm;
    let mut status: Result<(), IxgbeDriverErr> = Err(Eeprom);
    let mut i = 0;

    let swsm_offset = get_swsm_offset(info.get_id())?;
    // Get SMBI software semaphore between device drivers first
    while i < timeout {
        // If the SMBI bit is 0 when we read it, then the bit will be set and we have the semaphore
        swsm = ixgbe_hw::read_reg(info, swsm_offset)?;
        if swsm & IXGBE_SWSM_SMBI == 0 {
            status = Ok(());
            break;
        }
        wait_microsec(50);
        i += 1;
    }

    if i == timeout {
        release_eeprom_semaphore(info)?;

        wait_microsec(50);

        // one last try
        swsm = ixgbe_hw::read_reg(info, swsm_offset)?;
        if swsm & IXGBE_SWSM_SMBI == 0 {
            status = Ok(());
        }
    }

    // Get the semaphore between SW/FW
    if status.is_ok() {
        i = 0;
        while i < timeout {
            swsm = ixgbe_hw::read_reg(info, swsm_offset)?;

            // Set the SW EEPROM semaphore bit to request access
            swsm |= IXGBE_SWSM_SWESMBI;
            ixgbe_hw::write_reg(info, swsm_offset, swsm)?;

            // If we set the bit successfully then we got the semaphore.
            swsm = ixgbe_hw::read_reg(info, swsm_offset)?;
            if swsm & IXGBE_SWSM_SWESMBI != 0 {
                break;
            }

            wait_microsec(50);
            i += 1;
        }

        // Release semaphores and return error if SW EEPROM semaphore
        // was not granted because we don't have access to the EEPROM
        if i >= timeout {
            log::error!("SWESMBI Software EEPROM semaphore not granted.");
            release_eeprom_semaphore(info)?;
            status = Err(Eeprom);
        }
    } else {
        log::error!("Software semaphore SMBI between device drivers not granted.");
    }

    status
}

/// This function clears hardware semaphore bits.
fn release_eeprom_semaphore(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let mut swsm;
    let swsm_offset = get_swsm_offset(info.get_id())?;

    swsm = ixgbe_hw::read_reg(info, swsm_offset)?;

    // Release both semaphores by writing 0 to the bits SWESMBI and SMBI
    swsm &= !(IXGBE_SWSM_SWESMBI | IXGBE_SWSM_SMBI);

    ixgbe_hw::write_reg(info, swsm_offset, swsm)?;
    ixgbe_hw::write_flush(info)
}

/// ready_eeprom - Polls for EEPROM ready
fn ready_eeprom(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    // Read "Status Register" repeatedly until the LSB is cleared.  The
    // EEPROM will signal that the command has been completed by clearing
    // bit 0 of the internal status register.  If it's not cleared within
    // 5 milliseconds, then error out.
    let mut i = 0;
    while i < IXGBE_EEPROM_MAX_RETRY_SPI {
        shift_out_eeprom_bits(info, IXGBE_EEPROM_RDSR_OPCODE_SPI, IXGBE_EEPROM_OPCODE_BITS)?;
        let spi_stat_reg = shift_in_eeprom_bits(info, 8)? as u8;
        if spi_stat_reg & IXGBE_EEPROM_STATUS_RDY_SPI == 0 {
            break;
        }

        wait_microsec(5);
        standby_eeprom(info)?;
        i += 5;
    }

    // On some parts, SPI write time could vary from 0-20mSec on 3.3V
    // devices (and only 0-5mSec on 5V devices)
    if i >= IXGBE_EEPROM_MAX_RETRY_SPI {
        log::debug!("SPI EEPROM Status error\n");
        return Err(IxgbeDriverErr::Eeprom);
    }

    Ok(())
}

/// standby_eeprom - Returns EEPROM to a "standby" state
fn standby_eeprom(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let eec_offset = get_eec_offset(info.get_id())?;

    let mut eec = ixgbe_hw::read_reg(info, eec_offset)?;

    // Toggle CS to flush commands
    eec |= IXGBE_EEC_CS;
    ixgbe_hw::write_reg(info, eec_offset, eec)?;
    ixgbe_hw::write_flush(info)?;
    wait_microsec(1);
    eec &= !IXGBE_EEC_CS;
    ixgbe_hw::write_reg(info, eec_offset, eec)?;
    ixgbe_hw::write_flush(info)?;
    wait_microsec(1);

    Ok(())
}

/// shift_out_eeprom_bits - Shift data bits out to the EEPROM.
fn shift_out_eeprom_bits(info: &PCIeInfo, data: u16, count: u16) -> Result<(), IxgbeDriverErr> {
    let eec_offset = get_eec_offset(info.get_id())?;

    // Mask is used to shift "count" bits of "data" out to the EEPROM
    // one bit at a time.  Determine the starting bit based on count
    let mut mask = 0x01 << (count - 1);

    let mut eec = ixgbe_hw::read_reg(info, eec_offset)?;
    for _ in 0..count {
        // A "1" is shifted out to the EEPROM by setting bit "DI" to a
        // "1", and then raising and then lowering the clock (the SK
        // bit controls the clock input to the EEPROM).  A "0" is
        // shifted out to the EEPROM by setting "DI" to "0" and then
        // raising and then lowering the clock.
        if data & mask != 0 {
            eec |= IXGBE_EEC_DI;
        } else {
            eec &= !IXGBE_EEC_DI;
        }

        ixgbe_hw::write_reg(info, eec_offset, eec)?;
        ixgbe_hw::write_flush(info)?;

        wait_microsec(1);

        eec = raise_eeprom_clk(info, eec)?;
        eec = lower_eeprom_clk(info, eec)?;

        // Shift mask to signify next bit of data to shift in to the
        // EEPROM
        mask >>= 1;
    }

    // We leave the "DI" bit set to "0" when we leave this routine.
    eec &= !IXGBE_EEC_DI;
    ixgbe_hw::write_reg(info, eec_offset, eec)?;
    ixgbe_hw::write_flush(info)?;

    Ok(())
}

/// shift_in_eeprom_bits - Shift data bits in from the EEPROM
fn shift_in_eeprom_bits(info: &PCIeInfo, count: u16) -> Result<u16, IxgbeDriverErr> {
    let eec_offset = get_eec_offset(info.get_id())?;
    // In order to read a register from the EEPROM, we need to shift
    // 'count' bits in from the EEPROM. Bits are "shifted in" by raising
    // the clock input to the EEPROM (setting the SK bit), and then reading
    // the value of the "DO" bit.  During this "shifting in" process the
    // "DI" bit should always be clear.
    let mut eec = ixgbe_hw::read_reg(info, eec_offset)?;

    eec &= !(IXGBE_EEC_DO | IXGBE_EEC_DI);

    let mut data = 0;
    for _ in 0..count {
        data <<= 1;
        _ = raise_eeprom_clk(info, eec)?;

        eec = ixgbe_hw::read_reg(info, eec_offset)?;

        eec &= !(IXGBE_EEC_DI);
        if eec & IXGBE_EEC_DO != 0 {
            data |= 1;
        }

        eec = lower_eeprom_clk(info, eec)?;
    }

    Ok(data)
}

/// raise_eeprom_clk - Raises the EEPROM's clock input.
fn raise_eeprom_clk(info: &PCIeInfo, mut eec: u32) -> Result<u32, IxgbeDriverErr> {
    let eec_offset = get_eec_offset(info.get_id())?;
    // Raise the clock input to the EEPROM
    // (setting the SK bit), then delay
    eec |= IXGBE_EEC_SK;
    ixgbe_hw::write_reg(info, eec_offset, eec)?;
    ixgbe_hw::write_flush(info)?;
    wait_microsec(1);

    Ok(eec)
}

/// lower_eeprom_clk - Lowers the EEPROM's clock input.
fn lower_eeprom_clk(info: &PCIeInfo, mut eec: u32) -> Result<u32, IxgbeDriverErr> {
    let eec_offset = get_eec_offset(info.get_id())?;
    // Lower the clock input to the EEPROM (clearing the SK bit), then
    // delay
    eec &= !IXGBE_EEC_SK;
    ixgbe_hw::write_reg(info, eec_offset, eec)?;
    ixgbe_hw::write_flush(info)?;
    wait_microsec(1);

    Ok(eec)
}

/// read_eeprom_buffer_bit_bang - Read EEPROM using bit-bang
/// Reads 16 bit word(s) from EEPROM through bit-bang method
fn read_eeprom_buffer_bit_bang<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    eeprom: &mut IxgbeEepromInfo,
    offset: u16,
    data: &mut [u16],
) -> Result<(), IxgbeDriverErr> {
    log::debug!("read_eeprom_buffer_bit_bang");

    // Prepare the EEPROM for reading
    acquire_eeprom(ops, info, eeprom, |_ops| {
        if ready_eeprom(info).is_err() {
            return Err(IxgbeDriverErr::Eeprom);
        }

        let mut read_opcode = IXGBE_EEPROM_READ_OPCODE_SPI;
        for (i, d) in data.iter_mut().enumerate() {
            standby_eeprom(info)?;

            // Some SPI eeproms use the 8th address bit embedded
            // in the opcode
            if (eeprom.address_bits == 8) && ((offset + i as u16) >= 128) {
                read_opcode |= IXGBE_EEPROM_A8_OPCODE_SPI;
            }

            // Send the READ command (opcode + addr)
            shift_out_eeprom_bits(info, read_opcode as u16, IXGBE_EEPROM_OPCODE_BITS)?;
            shift_out_eeprom_bits(info, (offset + i as u16) * 2, eeprom.address_bits)?;

            // Read the data.
            let word_in = shift_in_eeprom_bits(info, 16)?;
            *d = word_in.rotate_left(8);
        }

        Ok(())
    })
}

/// read_eeprom_bit_bang_generic - Read EEPROM word using bit-bang
/// Reads 16 bit value from EEPROM through bit-bang method
pub fn read_eeprom_bit_bang_generic<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    eeprom: &mut IxgbeEepromInfo,
    offset: u16,
    data: &mut [u16],
) -> Result<(), IxgbeDriverErr> {
    log::debug!("read_eeprom_bit_bang_generic");

    if eeprom.eeprom_type == EepromType::IxgbeEepromUninitialized {
        ops.eeprom_init_params(info, eeprom)?;
        log::debug!("Eeprom params: {:?}", eeprom);
    }

    if offset >= eeprom.word_size {
        return Err(IxgbeDriverErr::Eeprom);
    }

    read_eeprom_buffer_bit_bang(ops, info, eeprom, offset, data)
}

pub fn phy_setup_link_generic<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    let (speed_supported, _autoneg) = get_copper_link_capabilities(ops, info, hw)?;

    // Set or unset auto-negotiation 10G advertisement
    let mut autoneg_reg = ops.phy_read_reg(
        info,
        hw,
        IXGBE_MII_10GBASE_T_AUTONEG_CTRL_REG,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
    )?;

    autoneg_reg &= !IXGBE_MII_10GBASE_T_ADVERTISE;
    if (hw.phy.autoneg_advertised & IXGBE_LINK_SPEED_10GB_FULL != 0)
        && (speed_supported & IXGBE_LINK_SPEED_10GB_FULL != 0)
    {
        autoneg_reg |= IXGBE_MII_10GBASE_T_ADVERTISE;
    }

    ops.phy_write_reg(
        info,
        hw,
        IXGBE_MII_10GBASE_T_AUTONEG_CTRL_REG,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
        autoneg_reg,
    )?;

    autoneg_reg = ops.phy_read_reg(
        info,
        hw,
        IXGBE_MII_AUTONEG_VENDOR_PROVISION_1_REG,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
    )?;

    if hw.mac.mac_type == MacType::IxgbeMacX550 {
        // Set or unset auto-negotiation 5G advertisement
        autoneg_reg &= !IXGBE_MII_5GBASE_T_ADVERTISE;
        if (hw.phy.autoneg_advertised & IXGBE_LINK_SPEED_5GB_FULL != 0)
            && (speed_supported & IXGBE_LINK_SPEED_5GB_FULL != 0)
        {
            autoneg_reg |= IXGBE_MII_5GBASE_T_ADVERTISE;
        }

        // Set or unset auto-negotiation 2.5G advertisement
        autoneg_reg &= !IXGBE_MII_2_5GBASE_T_ADVERTISE;
        if (hw.phy.autoneg_advertised & IXGBE_LINK_SPEED_2_5GB_FULL != 0)
            && (speed_supported & IXGBE_LINK_SPEED_2_5GB_FULL != 0)
        {
            autoneg_reg |= IXGBE_MII_2_5GBASE_T_ADVERTISE;
        }
    }

    // Set or unset auto-negotiation 1G advertisement
    autoneg_reg &= !IXGBE_MII_1GBASE_T_ADVERTISE;
    if (hw.phy.autoneg_advertised & IXGBE_LINK_SPEED_1GB_FULL != 0)
        && (speed_supported & IXGBE_LINK_SPEED_1GB_FULL != 0)
    {
        autoneg_reg |= IXGBE_MII_1GBASE_T_ADVERTISE;
    }

    ops.phy_write_reg(
        info,
        hw,
        IXGBE_MII_AUTONEG_VENDOR_PROVISION_1_REG,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
        autoneg_reg,
    )?;

    // Set or unset auto-negotiation 100M advertisement
    autoneg_reg = ops.phy_read_reg(
        info,
        hw,
        IXGBE_MII_AUTONEG_ADVERTISE_REG,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
    )?;

    autoneg_reg &= !(IXGBE_MII_100BASE_T_ADVERTISE | IXGBE_MII_100BASE_T_ADVERTISE_HALF);
    if (hw.phy.autoneg_advertised & IXGBE_LINK_SPEED_100_FULL != 0)
        && (speed_supported & IXGBE_LINK_SPEED_100_FULL != 0)
    {
        autoneg_reg |= IXGBE_MII_100BASE_T_ADVERTISE;
    }

    ops.phy_write_reg(
        info,
        hw,
        IXGBE_MII_AUTONEG_ADVERTISE_REG,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
        autoneg_reg,
    )?;

    // Blocked by MNG FW so don't reset PHY
    if check_reset_blocked(info, hw)? {
        return Ok(());
    }

    // Restart PHY auto-negotiation.
    autoneg_reg = ops.phy_read_reg(
        info,
        hw,
        IXGBE_MDIO_AUTO_NEG_CONTROL,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
    )?;

    autoneg_reg |= IXGBE_MII_RESTART;

    ops.phy_write_reg(
        info,
        hw,
        IXGBE_MDIO_AUTO_NEG_CONTROL,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
        autoneg_reg,
    )?;

    Ok(())
}

pub trait IxgbeOperations: Send {
    // MAC Operations

    fn mac_init_hw(&self, info: &mut PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        match self.mac_reset_hw(info, hw) {
            Ok(()) | Err(SfpNotPresent) => self.mac_start_hw(info, hw),
            Err(e) => Err(e),
        }
    }

    fn mac_reset_hw(&self, _info: &mut PCIeInfo, _hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        Ok(())
    }

    fn mac_start_hw(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr>;

    fn mac_get_media_type(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> MediaType;

    /// clear_vfta- Clear VLAN filter table
    /// Clears the VLAN filer table, and the VMDq index associated with the filter
    fn mac_clear_vfta(&self, info: &PCIeInfo, hw: &IxgbeHw) -> Result<(), IxgbeDriverErr> {
        for offset in 0..hw.mac.vft_size {
            ixgbe_hw::write_reg(info, IXGBE_VFTA(offset as usize), 0)?;
        }

        for offset in 0..IXGBE_VLVF_ENTRIES {
            ixgbe_hw::write_reg(info, IXGBE_VLVF(offset) as usize, 0)?;
            ixgbe_hw::write_reg(info, IXGBE_VLVFB(offset * 2) as usize, 0)?;
            ixgbe_hw::write_reg(info, IXGBE_VLVFB((offset * 2) + 1) as usize, 0)?;
        }

        Ok(())
    }

    /// mac_clear_hw_cntrs - Generic clear hardware counters
    /// Clears all hardware statistics counters by reading them from the hardware
    /// Statistics counters are clear on read.
    fn mac_clear_hw_cntrs(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::{read_reg, MacType::*};

        read_reg(info, IXGBE_CRCERRS)?;
        read_reg(info, IXGBE_ILLERRC)?;
        read_reg(info, IXGBE_ERRBC)?;
        read_reg(info, IXGBE_MSPDC)?;
        for i in 0..8 {
            read_reg(info, IXGBE_MPC(i))?;
        }

        read_reg(info, IXGBE_MLFC)?;
        read_reg(info, IXGBE_MRFC)?;
        read_reg(info, IXGBE_RLEC)?;
        read_reg(info, IXGBE_LXONTXC)?;
        read_reg(info, IXGBE_LXOFFTXC)?;

        if hw.mac.mac_type >= IxgbeMac82599EB {
            read_reg(info, IXGBE_LXONRXCNT)?;
            read_reg(info, IXGBE_LXOFFRXCNT)?;
        } else {
            read_reg(info, IXGBE_LXONRXC)?;
            read_reg(info, IXGBE_LXOFFRXC)?;
        }

        for i in 0..8 {
            read_reg(info, IXGBE_PXONTXC(i))?;
            read_reg(info, IXGBE_PXOFFTXC(i))?;
            if hw.mac.mac_type >= IxgbeMac82599EB {
                read_reg(info, IXGBE_PXONRXCNT(i))?;
                read_reg(info, IXGBE_PXOFFRXCNT(i))?;
            } else {
                read_reg(info, IXGBE_PXONRXC(i))?;
                read_reg(info, IXGBE_PXOFFRXC(i))?;
            }
        }
        if hw.mac.mac_type >= IxgbeMac82599EB {
            for i in 0..8 {
                read_reg(info, IXGBE_PXON2OFFCNT(i))?;
            }
        }

        read_reg(info, IXGBE_PRC64)?;
        read_reg(info, IXGBE_PRC127)?;
        read_reg(info, IXGBE_PRC255)?;
        read_reg(info, IXGBE_PRC511)?;
        read_reg(info, IXGBE_PRC1023)?;
        read_reg(info, IXGBE_PRC1522)?;
        read_reg(info, IXGBE_GPRC)?;
        read_reg(info, IXGBE_BPRC)?;
        read_reg(info, IXGBE_MPRC)?;
        read_reg(info, IXGBE_GPTC)?;
        read_reg(info, IXGBE_GORCL)?;
        read_reg(info, IXGBE_GORCH)?;
        read_reg(info, IXGBE_GOTCL)?;
        read_reg(info, IXGBE_GOTCH)?;

        if hw.mac.mac_type == IxgbeMac82598EB {
            for i in 0..8 {
                read_reg(info, IXGBE_RNBC(i))?;
            }
        }

        read_reg(info, IXGBE_RUC)?;
        read_reg(info, IXGBE_RFC)?;
        read_reg(info, IXGBE_ROC)?;
        read_reg(info, IXGBE_RJC)?;
        read_reg(info, IXGBE_MNGPRC)?;
        read_reg(info, IXGBE_MNGPDC)?;
        read_reg(info, IXGBE_MNGPTC)?;
        read_reg(info, IXGBE_TORL)?;
        read_reg(info, IXGBE_TORH)?;
        read_reg(info, IXGBE_TPR)?;
        read_reg(info, IXGBE_TPT)?;
        read_reg(info, IXGBE_PTC64)?;
        read_reg(info, IXGBE_PTC127)?;
        read_reg(info, IXGBE_PTC255)?;
        read_reg(info, IXGBE_PTC511)?;
        read_reg(info, IXGBE_PTC1023)?;
        read_reg(info, IXGBE_PTC1522)?;
        read_reg(info, IXGBE_MPTC)?;
        read_reg(info, IXGBE_BPTC)?;
        for i in 0..16 {
            read_reg(info, IXGBE_QPRC(i))?;
            read_reg(info, IXGBE_QPTC(i))?;
            if hw.mac.mac_type >= IxgbeMac82599EB {
                read_reg(info, IXGBE_QBRC_L(i))?;
                read_reg(info, IXGBE_QBRC_H(i))?;
                read_reg(info, IXGBE_QBTC_L(i))?;
                read_reg(info, IXGBE_QBTC_H(i))?;
                read_reg(info, IXGBE_QPRDC(i))?;
            } else {
                read_reg(info, IXGBE_QBRC(i))?;
                read_reg(info, IXGBE_QBTC(i))?;
            }
        }

        if hw.mac.mac_type == IxgbeMacX550 || hw.mac.mac_type == IxgbeMacX540 {
            if hw.phy.id == 0 {
                // Does not use the return value.
                // https://github.com/openbsd/src/blob/c04d1b34942009a09b1284605d539f1382aa35bb/sys/dev/pci/ixgbe.c#L657
                let _ = self.phy_identify(info, hw);
            }
            self.phy_read_reg(info, hw, IXGBE_PCRC8ECL, IXGBE_MDIO_PCS_DEV_TYPE)?;
            self.phy_read_reg(info, hw, IXGBE_PCRC8ECH, IXGBE_MDIO_PCS_DEV_TYPE)?;
            self.phy_read_reg(info, hw, IXGBE_LDPCECL, IXGBE_MDIO_PCS_DEV_TYPE)?;
            self.phy_read_reg(info, hw, IXGBE_LDPCECH, IXGBE_MDIO_PCS_DEV_TYPE)?;
        }

        Ok(())
    }

    fn mac_get_mac_addr(&self, info: &PCIeInfo, mac_addr: &mut [u8]) -> Result<(), IxgbeDriverErr> {
        let rar_high = ixgbe_hw::read_reg(info, IXGBE_RAH(0) as usize)?;
        let rar_low = ixgbe_hw::read_reg(info, IXGBE_RAL(0) as usize)?;

        #[allow(clippy::needless_range_loop)]
        for i in 0..4 {
            mac_addr[i] = (rar_low >> (i * 8)) as u8;
        }
        for i in 0..2 {
            mac_addr[i + 4] = (rar_high >> (i * 8)) as u8;
        }

        Ok(())
    }

    /// stop_adapter - Stop Tx/Rx units
    /// Sets the adapter_stopped flag within ixgbe_hw struct. Clears interrupts,
    /// disables transmit and receive units. The adapter_stopped flag is used by
    /// the shared code and drivers to determine if the adapter is in a stopped
    /// state and should not touch the hardware.
    fn mac_stop_adapter(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IxgbeHw,
    ) -> Result<(), IxgbeDriverErr> {
        // Set the adapter_stopped flag so other driver functions stop touching the hardware
        hw.adapter_stopped = true;
        // Disable the receive unit
        self.mac_disable_rx(info, hw)?;

        // Clear interrupt mask to stop interrupts from being generated
        ixgbe_hw::write_reg(info, IXGBE_EIMC, IXGBE_IRQ_CLEAR_MASK)?;

        // Clear any pending interrupts, flush previous writes
        ixgbe_hw::read_reg(info, IXGBE_EICR)?;

        // Disable the transmit unit.  Each queue must be disabled.
        for i in 0..hw.mac.max_tx_queues {
            ixgbe_hw::write_reg(info, IXGBE_TXDCTL(i as usize), IXGBE_TXDCTL_SWFLSH)?;
        }
        // Disable the receive unit by stopping each queue
        let mut reg_val;
        for i in 0..hw.mac.max_rx_queues {
            reg_val = ixgbe_hw::read_reg(info, IXGBE_RXDCTL(i as usize))?;
            reg_val &= !IXGBE_RXDCTL_ENABLE;
            reg_val |= IXGBE_RXDCTL_SWFLSH;
            ixgbe_hw::write_reg(info, IXGBE_RXDCTL(i as usize), reg_val)?;
        }

        // flush all queues disables
        ixgbe_hw::write_flush(info)?;
        wait_millisec(2);

        // Prevent the PCI-E bus from hanging by disabling PCI-E master
        // access and verify no pending requests

        disable_pcie_master(info, hw)?;

        Ok(())
    }

    /// mac_init_rx_addrs_generic - Initializes receive address filters.
    /// Places the MAC address in receive address register 0 and clears the rest
    /// of the receive address registers. Clears the multicast table. Assumes
    /// the receiver is in reset when the routine is called.
    fn mac_init_rx_addrs(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        // If the current mac address is valid, assume it is a software override
        // to the permanent address.
        // Otherwise, use the permanent address from the eeprom.
        if validate_mac_addr(&hw.mac.addr) == Err(InvalidMacAddr) {
            // Get the MAC address from the RAR0 for later reference
            self.mac_get_mac_addr(info, &mut hw.mac.addr)?;
        } else {
            // Setup the receive address.
            self.mac_set_rar(
                info,
                hw.mac.num_rar_entries,
                0,
                &hw.mac.addr,
                0,
                IXGBE_RAH_AV,
            )?;
        }

        // clear VMDq pool/queue selection for RAR 0
        self.mac_clear_vmdq(info, hw.mac.num_rar_entries, 0, IXGBE_CLEAR_VMDQ_ALL)?;

        hw.addr_ctrl.overflow_promisc = 0;
        hw.addr_ctrl.rar_used_count = 1;

        // Zero out the other receive addresses.
        for i in 1..hw.mac.num_rar_entries {
            ixgbe_hw::write_reg(info, IXGBE_RAL(i) as usize, 0)?;
            ixgbe_hw::write_reg(info, IXGBE_RAH(i) as usize, 0)?;
        }

        // Clear the MTA
        hw.addr_ctrl.mta_in_use = 0;
        ixgbe_hw::write_reg(info, IXGBE_MCSTCTRL, hw.mac.mc_filter_type as u32)?;

        for i in 0..hw.mac.mcft_size {
            ixgbe_hw::write_reg(info, IXGBE_MTA(i) as usize, 0)?;
        }

        self.mac_init_uta_tables(info)?;

        Ok(())
    }

    /// clear_rar_generic - Remove Rx address register
    /// Clears an ethernet address from a receive address register.
    fn mac_clear_rar(
        &self,
        info: &PCIeInfo,
        num_rar_entries: u32,
        index: u32,
    ) -> Result<(), IxgbeDriverErr> {
        // Make sure we are using a valid rar index range
        if index >= num_rar_entries {
            log::error!("RAR index {} is out of range.\n", index);
            return Err(InvalidArgument);
        }

        // Some parts put the VMDq setting in the extra RAH bits,
        // so save everything except the lower 16 bits that hold part
        // of the address and the address valid bit.
        let mut rar_high = ixgbe_hw::read_reg(info, IXGBE_RAH(index) as usize)?;
        rar_high &= !(0x0000FFFF | IXGBE_RAH_AV);

        ixgbe_hw::write_reg(info, IXGBE_RAL(index) as usize, 0)?;
        ixgbe_hw::write_reg(info, IXGBE_RAH(index) as usize, rar_high)?;

        // clear VMDq pool/queue selection for this RAR
        self.mac_clear_vmdq(info, num_rar_entries, index, IXGBE_CLEAR_VMDQ_ALL)?;

        Ok(())
    }

    /// mac_set_rar - Set Rx address register
    /// Puts an ethernet address into a receive address register.
    fn mac_set_rar(
        &self,
        info: &PCIeInfo,
        num_rar_entries: u32,
        index: u32,
        addr: &[u8],
        vmdq: u32,
        enable_addr: u32,
    ) -> Result<(), IxgbeDriverErr> {
        // Make sure we are using a valid rar index range
        if index >= num_rar_entries {
            log::error!("RAR index {} is out of range.\n", index);
            return Err(IxgbeDriverErr::InvalidArgument);
        }

        // setup VMDq pool selection before this RAR gets enabled
        self.mac_set_vmdq(info, num_rar_entries, index, vmdq)?;

        // HW expects these in little endian so we reverse the byte
        // order from network order (big endian) to little endian
        let rar_low = addr[0] as u32
            | ((addr[1] as u32) << 8)
            | ((addr[2] as u32) << 16)
            | ((addr[3] as u32) << 24);

        // Some parts put the VMDq setting in the extra RAH bits,
        // so save everything except the lower 16 bits that hold part
        // of the address and the address valid bit.
        let mut rar_high = ixgbe_hw::read_reg(info, IXGBE_RAH(index) as usize)?;
        rar_high &= !(0x0000FFFF | IXGBE_RAH_AV);
        rar_high |= (addr[4] as u32) | ((addr[5] as u32) << 8);

        if enable_addr != 0 {
            rar_high |= IXGBE_RAH_AV;
        }

        ixgbe_hw::write_reg(info, IXGBE_RAL(index) as usize, rar_low)?;
        ixgbe_hw::write_reg(info, IXGBE_RAH(index) as usize, rar_high)?;

        Ok(())
    }

    /// mac_set_vmdq - Associate a VMDq pool index with a rx address
    fn mac_set_vmdq(
        &self,
        info: &PCIeInfo,
        num_rar_entries: u32,
        rar: u32,
        vmdq: u32,
    ) -> Result<(), IxgbeDriverErr> {
        // Make sure we are using a valid rar index range.
        if rar >= num_rar_entries {
            return Err(InvalidArgument);
        }

        let mut mpsar;
        if vmdq < 32 {
            mpsar = ixgbe_hw::read_reg(info, IXGBE_MPSAR_LO(rar) as usize)?;
            mpsar |= 1 << vmdq;
            ixgbe_hw::write_reg(info, IXGBE_MPSAR_LO(rar) as usize, mpsar)?;
        } else {
            mpsar = ixgbe_hw::read_reg(info, IXGBE_MPSAR_HI(rar) as usize)?;
            mpsar |= 1 << (vmdq - 32);
            ixgbe_hw::write_reg(info, IXGBE_MPSAR_HI(rar) as usize, mpsar)?;
        }

        Ok(())
    }

    /// mac_clear_vmdq - Disassociate a VMDq pool index from a rx address
    fn mac_clear_vmdq(
        &self,
        info: &PCIeInfo,
        num_rar_entries: u32,
        rar: u32,
        vmdq: u32,
    ) -> Result<(), IxgbeDriverErr> {
        // Make sure we are using a valid rar index range
        if rar >= num_rar_entries {
            return Err(InvalidArgument);
        }

        let mut mpsar_lo = ixgbe_hw::read_reg(info, IXGBE_MPSAR_LO(rar) as usize)?;
        let mut mpsar_hi = ixgbe_hw::read_reg(info, IXGBE_MPSAR_HI(rar) as usize)?;

        if mpsar_lo == 0 && !mpsar_hi == 0 {
            return Ok(());
        }

        if vmdq == IXGBE_CLEAR_VMDQ_ALL {
            if mpsar_lo != 0 {
                ixgbe_hw::write_reg(info, IXGBE_MPSAR_LO(rar) as usize, 0)?;
                mpsar_lo = 0;
            }
            if mpsar_hi != 0 {
                ixgbe_hw::write_reg(info, IXGBE_MPSAR_HI(rar) as usize, 0)?;
                mpsar_hi = 0;
            }
        } else if vmdq < 32 {
            mpsar_lo &= !(1 << vmdq);
            ixgbe_hw::write_reg(info, IXGBE_MPSAR_LO(rar) as usize, mpsar_lo)?;
        } else {
            mpsar_hi &= !(1 << (vmdq - 32));
            ixgbe_hw::write_reg(info, IXGBE_MPSAR_HI(rar) as usize, mpsar_hi)?;
        }

        // was that the last pool using this rar?
        if mpsar_lo == 0 && mpsar_hi == 0 && rar != 0 {
            self.mac_clear_rar(info, num_rar_entries, rar)?;
        }

        Ok(())
    }

    /// mac_init_uta_tables - Initialize the Unicast Table Array
    fn mac_init_uta_tables(&self, info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
        for i in 0..128 {
            ixgbe_hw::write_reg(info, IXGBE_UTA(i), 0)?;
        }
        Ok(())
    }

    /// mac_setup_fc - Set up flow control
    /// Called at init time to set up flow control.
    fn mac_setup_fc(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::{FcMode::*, MediaType::*};
        // Validate the requested mode
        if hw.fc.strict_ieee && hw.fc.requested_mode == IxgbeFcRxPause {
            return Err(InvalidLinkSettings);
        }

        // 10gig parts do not have a word in the EEPROM to determine the
        // default flow control setting, so we explicitly set it to full.
        if hw.fc.requested_mode == IxgbeFcDefault {
            hw.fc.requested_mode = IxgbeFcFull;
        }

        // Set up the 1G and 10G flow control advertisement registers so the
        // HW will be able to do fc autoneg once the cable is plugged in.  If
        // we link at 10G, the 1G advertisement is harmless and vice versa.
        let mut reg;
        let mut reg_bp;
        let mut reg_cu;
        (reg, reg_bp, reg_cu) = match hw.phy.media_type {
            IxgbeMediaTypeBackplane =>
            // some MAC's need RMW protection on AUTOC
            {
                (
                    ixgbe_hw::read_reg(info, IXGBE_PCS1GANA)?,
                    self.mac_prot_autoc_read(info)?,
                    0,
                )
            }
            // only backplane uses autoc so fall though
            IxgbeMediaTypeFiberFixed | IxgbeMediaTypeFiberQsfp | IxgbeMediaTypeFiber => {
                (ixgbe_hw::read_reg(info, IXGBE_PCS1GANA)?, 0, 0)
            }
            IxgbeMediaTypeCopper => (
                0,
                0,
                self.phy_read_reg(
                    info,
                    hw,
                    IXGBE_MDIO_AUTO_NEG_ADVT,
                    IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
                )? as u32,
            ),
            _ => (0, 0, 0),
        };
        /*
         * The possible values of fc.requested_mode are:
         * 0: Flow control is completely disabled
         * 1: Rx flow control is enabled (we can receive pause frames,
         *    but not send pause frames).
         * 2: Tx flow control is enabled (we can send pause frames but
         *    we do not support receiving pause frames).
         * 3: Both Rx and Tx flow control (symmetric) are enabled.
         * other: Invalid.
         */
        (reg, reg_bp, reg_cu) = match hw.fc.requested_mode {
	        IxgbeFcNone => {
		        // Flow control completely disabled by software override.
		        reg &= !(IXGBE_PCS1GANA_SYM_PAUSE | IXGBE_PCS1GANA_ASM_PAUSE);
		        match hw.phy.media_type {
                IxgbeMediaTypeBackplane =>
			        (reg, reg_bp & !(IXGBE_AUTOC_SYM_PAUSE |
				            IXGBE_AUTOC_ASM_PAUSE), reg_cu),
		        IxgbeMediaTypeCopper =>
			        (reg, reg_bp, reg_cu & !(IXGBE_TAF_SYM_PAUSE | IXGBE_TAF_ASM_PAUSE)),
                _ => (reg, reg_bp, reg_cu),
                }
            }
	        IxgbeFcTxPause => {
		        // Tx Flow control is enabled, and Rx Flow control is
		        // disabled by software override.
		        reg |= IXGBE_PCS1GANA_ASM_PAUSE;
		        reg &= !IXGBE_PCS1GANA_SYM_PAUSE;
		        match hw.phy.media_type {
                IxgbeMediaTypeBackplane =>
			        (reg, (reg_bp | IXGBE_AUTOC_ASM_PAUSE) & !IXGBE_AUTOC_SYM_PAUSE, reg_cu),
		        IxgbeMediaTypeCopper =>
			        (reg, reg_bp, (reg_cu | IXGBE_TAF_ASM_PAUSE) & !IXGBE_TAF_SYM_PAUSE),
                _ => (reg, reg_bp, reg_cu),
                }
            }
	        IxgbeFcRxPause |
		        // Rx Flow control is enabled and Tx Flow control is
		        // disabled by software override. Since there really
		        // isn't a way to advertise that we are capable of RX
		        // Pause ONLY, we will advertise that we support both
		        // symmetric and asymmetric Rx PAUSE, as such we fall
		        // through to the fc_full statement.  Later, we will
		        // disable the adapter's ability to send PAUSE frames.
	        IxgbeFcFull => {
		        // Flow control (both Rx and Tx) is enabled by SW override.
		        reg |= IXGBE_PCS1GANA_SYM_PAUSE | IXGBE_PCS1GANA_ASM_PAUSE;
		        match hw.phy.media_type {
                IxgbeMediaTypeBackplane =>
			        (reg, reg_bp | IXGBE_AUTOC_SYM_PAUSE | IXGBE_AUTOC_ASM_PAUSE, reg_cu),
		        IxgbeMediaTypeCopper =>
			        (reg, reg_bp, reg_cu | IXGBE_TAF_SYM_PAUSE | IXGBE_TAF_ASM_PAUSE),
                _ => (reg, reg_bp, reg_cu),
                }
            }
	        _ =>{
                log::error!("Flow control param set incorrectly\n");
                return Err(Config);
            }
	    };

        if hw.mac.mac_type < MacType::IxgbeMacX540 {
            // Enable auto-negotiation between the MAC & PHY;
            // the MAC will advertise clause 37 flow control.
            ixgbe_hw::write_reg(info, IXGBE_PCS1GANA, reg)?;
            reg = ixgbe_hw::read_reg(info, IXGBE_PCS1GLCTL)?;

            // Disable AN timeout
            if hw.fc.strict_ieee {
                reg &= !IXGBE_PCS1GLCTL_AN_1G_TIMEOUT_EN;
            }

            ixgbe_hw::write_reg(info, IXGBE_PCS1GLCTL, reg)?;
        }

        // AUTOC restart handles negotiation of 1G and 10G on backplane
        // and copper. There is no need to set the PCS1GCTL register.
        if hw.phy.media_type == IxgbeMediaTypeBackplane {
            reg_bp |= IXGBE_AUTOC_AN_RESTART;
            self.mac_prot_autoc_write(info, hw, reg_bp)?;
        } else if (hw.phy.media_type == IxgbeMediaTypeCopper)
            && device_supports_autoneg_fc(self, info, hw)?
        {
            self.phy_write_reg(
                info,
                hw,
                IXGBE_MDIO_AUTO_NEG_ADVT,
                IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
                reg_cu as u16,
            )?;
        }

        Ok(())
    }

    /// mac_fc_enable - Enable flow control
    /// Enable flow control according to the current settings.
    fn mac_fc_enable(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::FcMode::*;

        // Validate the water mark configuration
        if hw.fc.pause_time == 0 {
            return Err(InvalidLinkSettings);
        }

        // Low water mark of zero causes XOFF floods
        for i in 0..IXGBE_DCB_MAX_TRAFFIC_CLASS {
            if ((hw.fc.current_mode == IxgbeFcTxPause || hw.fc.current_mode == IxgbeFcFull)
                && (hw.fc.high_water[i] != 0))
                && ((hw.fc.low_water[i] == 0) || (hw.fc.low_water[i] >= hw.fc.high_water[i]))
            {
                log::debug!("Invalid water mark configuration");
                return Err(InvalidLinkSettings);
            }
        }

        // Negotiate the fc mode to use
        self.mac_fc_autoneg(info, hw)?;

        // Disable any previous flow control settings
        let mut mflcn_reg = ixgbe_hw::read_reg(info, IXGBE_MFLCN)?;
        mflcn_reg &= !(IXGBE_MFLCN_RPFCE_MASK | IXGBE_MFLCN_RFCE);

        let mut fccfg_reg = ixgbe_hw::read_reg(info, IXGBE_FCCFG)?;
        fccfg_reg &= !(IXGBE_FCCFG_TFCE_802_3X | IXGBE_FCCFG_TFCE_PRIORITY);

        // The possible values of fc.current_mode are:
        // 0: Flow control is completely disabled
        // 1: Rx flow control is enabled (we can receive pause frames,
        //    but not send pause frames).
        // 2: Tx flow control is enabled (we can send pause frames but
        //    we do not support receiving pause frames).
        // 3: Both Rx and Tx flow control (symmetric) are enabled.
        // other: Invalid.
        (mflcn_reg, fccfg_reg) = match hw.fc.current_mode {
            // Flow control is disabled by software override or autoneg.
            // The code below will actually disable it in the HW.
            IxgbeFcNone => (mflcn_reg, fccfg_reg),
            // Rx Flow control is enabled and Tx Flow control is
            // disabled by software override. Since there really
            // isn't a way to advertise that we are capable of RX
            // Pause ONLY, we will advertise that we support both
            // symmetric and asymmetric Rx PAUSE.  Later, we will
            // disable the adapter's ability to send PAUSE frames.
            IxgbeFcRxPause => (mflcn_reg | IXGBE_MFLCN_RFCE, fccfg_reg),
            // Tx Flow control is enabled, and Rx Flow control is
            // disabled by software override.
            IxgbeFcTxPause => (mflcn_reg, fccfg_reg | IXGBE_FCCFG_TFCE_802_3X),
            // Flow control (both Rx and Tx) is enabled by SW override.
            IxgbeFcFull => (
                mflcn_reg | IXGBE_MFLCN_RFCE,
                fccfg_reg | IXGBE_FCCFG_TFCE_802_3X,
            ),
            _ => {
                log::error!("Flow control param set incorrectly");
                return Err(Config);
            }
        };

        // Set 802.3x based flow control settings.
        mflcn_reg |= IXGBE_MFLCN_DPF;
        ixgbe_hw::write_reg(info, IXGBE_MFLCN, mflcn_reg)?;
        ixgbe_hw::write_reg(info, IXGBE_FCCFG, fccfg_reg)?;

        // Set up and enable Rx high/low water mark thresholds, enable XON.
        let mut fcrtl;
        let mut fcrth;
        for i in 0..IXGBE_DCB_MAX_TRAFFIC_CLASS {
            if (hw.fc.current_mode == IxgbeFcTxPause || hw.fc.current_mode == IxgbeFcFull)
                && hw.fc.high_water[i] != 0
            {
                fcrtl = (hw.fc.low_water[i] << 10) | IXGBE_FCRTL_XONE;
                ixgbe_hw::write_reg(info, IXGBE_FCRTL_82599(i), fcrtl)?;
                fcrth = (hw.fc.high_water[i] << 10) | IXGBE_FCRTH_FCEN;
            } else {
                ixgbe_hw::write_reg(info, IXGBE_FCRTL_82599(i), 0)?;
                // In order to prevent Tx hangs when the internal Tx
                // switch is enabled we must set the high water mark
                // to the Rx packet buffer size - 24KB.  This allows
                // the Tx switch to function even under heavy Rx
                // workloads.
                fcrth = ixgbe_hw::read_reg(info, IXGBE_RXPBSIZE(i))? - 0x6000;
            }

            ixgbe_hw::write_reg(info, IXGBE_FCRTH_82599(i), fcrth)?;
        }

        // Configure pause time (2 TCs per register)
        let reg = hw.fc.pause_time as u32 * 0x00010001;
        for i in 0..IXGBE_DCB_MAX_TRAFFIC_CLASS / 2 {
            ixgbe_hw::write_reg(info, IXGBE_FCTTV(i), reg)?;
        }

        // Configure flow control refresh threshold value
        ixgbe_hw::write_reg(info, IXGBE_FCRTV, hw.fc.pause_time as u32 / 2)?;

        Ok(())
    }

    /// mac_fc_autoneg - Configure flow control
    /// Compares our advertised flow control capabilities to those advertised by
    /// our link partner, and determines the proper flow control mode to use.
    fn mac_fc_autoneg(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MediaType::*;

        // AN should have completed when the cable was plugged in.
        // Look for reasons to bail out.  Bail out if:
        //- FC autoneg is disabled, or if
        //- link is not up.
        if hw.fc.disable_fc_autoneg {
            log::error!("Flow control autoneg is disabled");
            hw.fc.fc_was_autonegged = false;
            hw.fc.current_mode = hw.fc.requested_mode;
            return Err(FcNotNegotiated);
        }

        let (speed, link_up) = self.mac_check_link(info, hw, false)?;
        if !link_up {
            log::error!("The link is down");
            hw.fc.fc_was_autonegged = false;
            hw.fc.current_mode = hw.fc.requested_mode;
            return Err(FcNotNegotiated);
        }

        match hw.phy.media_type {
            // Autoneg flow control on fiber adapters
            IxgbeMediaTypeFiber | IxgbeMediaTypeFiberFixed | IxgbeMediaTypeFiberQsfp => {
                if speed == IXGBE_LINK_SPEED_1GB_FULL {
                    fc_autoneg_fiber(info, hw)?;
                } else {
                    return Err(FcNotNegotiated);
                }
            }
            // Autoneg flow control on backplane adapters
            IxgbeMediaTypeBackplane => {
                fc_autoneg_backplane(info, hw)?;
            }
            // Autoneg flow control on copper adapters
            IxgbeMediaTypeCopper => {
                if device_supports_autoneg_fc(self, info, hw)? {
                    fc_autoneg_copper(self, info, hw)?;
                } else {
                    return Err(FcNotNegotiated);
                }
            }
            _ => (),
        }

        hw.fc.fc_was_autonegged = true;

        Ok(())
    }

    /// mac_check_link - Determine link and speed status
    /// Reads the links register to determine if link is up and the current speed
    fn mac_check_link(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
        link_up_wait_to_complete: bool,
    ) -> Result<(u32, bool), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;

        /* If Crosstalk fix enabled do the sanity check of making sure
         * the SFP+ cage is full.
         */
        if need_crosstalk_fix(self, info, hw) {
            let sfp_cage_full = match hw.mac.mac_type {
                IxgbeMac82599EB => ixgbe_hw::read_reg(info, IXGBE_ESDP)? & IXGBE_ESDP_SDP2,
                IxgbeMacX550EMX | IxgbeMacX550EMA => {
                    ixgbe_hw::read_reg(info, IXGBE_ESDP)? & IXGBE_ESDP_SDP0
                }
                _ => 0, /* sanity check - No SFP+ devices here */
            };

            if sfp_cage_full == 0 {
                return Ok((IXGBE_LINK_SPEED_UNKNOWN, false));
            }
        }

        // clear the old state
        let links_orig = ixgbe_hw::read_reg(info, IXGBE_LINKS)?;

        let mut links_reg = ixgbe_hw::read_reg(info, IXGBE_LINKS)?;

        if links_orig != links_reg {
            log::debug!("LINKS changed from {:?} to {:?}\n", links_orig, links_reg);
        }

        let mut link_up = false;
        #[allow(clippy::collapsible_else_if)]
        if link_up_wait_to_complete {
            for _ in 0..hw.mac.max_link_up_time {
                if links_reg & IXGBE_LINKS_UP != 0 {
                    link_up = true;
                    break;
                } else {
                    link_up = false;
                }
                wait_millisec(100);
                links_reg = ixgbe_hw::read_reg(info, IXGBE_LINKS)?;
            }
        } else {
            link_up = links_reg & IXGBE_LINKS_UP != 0;
        }

        let speed = match links_reg & IXGBE_LINKS_SPEED_82599 {
            IXGBE_LINKS_SPEED_10G_82599 => {
                if hw.mac.mac_type >= IxgbeMacX550 && links_reg & IXGBE_LINKS_SPEED_NON_STD != 0 {
                    IXGBE_LINK_SPEED_2_5GB_FULL
                } else {
                    IXGBE_LINK_SPEED_10GB_FULL
                }
            }
            IXGBE_LINKS_SPEED_1G_82599 => IXGBE_LINK_SPEED_1GB_FULL,
            IXGBE_LINKS_SPEED_100_82599 => {
                if hw.mac.mac_type == IxgbeMacX550 && links_reg & IXGBE_LINKS_SPEED_NON_STD != 0 {
                    IXGBE_LINK_SPEED_5GB_FULL
                } else {
                    IXGBE_LINK_SPEED_100_FULL
                }
            }
            IXGBE_LINKS_SPEED_10_X550EM_A => {
                if info.id == IXGBE_DEV_ID_X550EM_A_1G_T || info.id == IXGBE_DEV_ID_X550EM_A_1G_T_L
                {
                    IXGBE_LINK_SPEED_10_FULL
                } else {
                    IXGBE_LINK_SPEED_UNKNOWN
                }
            }
            _ => IXGBE_LINK_SPEED_UNKNOWN,
        };

        Ok((speed, link_up))
    }

    fn mac_prot_autoc_read(&self, info: &PCIeInfo) -> Result<u32, IxgbeDriverErr> {
        ixgbe_hw::read_reg(info, IXGBE_AUTOC)
    }

    fn mac_prot_autoc_write(
        &self,
        info: &PCIeInfo,
        _hw: &mut IxgbeHw,
        reg_val: u32,
    ) -> Result<(), IxgbeDriverErr> {
        ixgbe_hw::write_reg(info, IXGBE_AUTOC, reg_val)
    }

    fn mac_get_device_caps(&self, info: &PCIeInfo) -> Result<u32, IxgbeDriverErr> {
        ixgbe_hw::read_reg(info, IXGBE_DEVICE_CAPS)
    }

    /// mac_set_lan_id - Set LAN id for PCIe multiple port devices
    /// Determines the LAN function id by reading memory-mapped registers and swaps
    /// the port value if requested, and set MAC instance for devices that share
    /// CS4227.
    /// Doesn't suport X550EM_a currently
    /// ixgbe_set_lan_id_multi_port_pcie in OpenBSD
    fn mac_set_lan_id(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
    ) -> Result<(u16, u8, u16), IxgbeDriverErr> {
        let mut reg = ixgbe_hw::read_reg(info, IXGBE_STATUS)?;
        let mut func = ((reg & IXGBE_STATUS_LAN_ID) >> IXGBE_STATUS_LAN_ID_SHIFT) as u16;
        let lan_id = func as u8;
        let factps_offset = get_factps_offset(info.get_id())?;

        // check for a port swap
        reg = ixgbe_hw::read_reg(info, factps_offset)?;
        if reg & IXGBE_FACTPS_LFS != 0 {
            func ^= 0x1;
        }

        // Get MAC instance from EEPROM for configuring CS4227
        let mut ee_ctrl_4 = [0; 1];
        let mut instance_id = 0;
        if info.id == IXGBE_DEV_ID_X550EM_A_SFP {
            self.eeprom_read(info, &mut hw.eeprom, IXGBE_EEPROM_CTRL_4, &mut ee_ctrl_4)?;
            instance_id = (ee_ctrl_4[0] & IXGBE_EE_CTRL_4_INST_ID) >> IXGBE_EE_CTRL_4_INST_ID_SHIFT;
        }

        Ok((func, lan_id, instance_id))
    }

    /// mac_acquire_swhw_sync() - Acquire SWFW semaphore
    /// Acquires the SWFW semaphore through the GSSR register for the specified function (CSR, PHY0, PHY1, EEPROM, Flash)
    fn mac_acquire_swfw_sync(&self, info: &PCIeInfo, mask: u32) -> Result<(), IxgbeDriverErr> {
        let mut gssr = 0;
        let timeout = 200;
        let swmask = mask;
        let fwmask = mask << 5;

        for _ in 0..timeout {
            // SW NVM semaphore bit is used for access to all
            // SW_FW_SYNC bits (not just NVM)

            get_eeprom_semaphore(info)?;

            gssr = match ixgbe_hw::read_reg(info, IXGBE_GSSR) {
                Err(e) => {
                    release_eeprom_semaphore(info)?;
                    return Err(e);
                }
                Ok(ret) => ret,
            };

            if !(gssr & (fwmask | swmask)) != 0 {
                gssr |= swmask;
                let result = ixgbe_hw::write_reg(info, IXGBE_GSSR, gssr);
                release_eeprom_semaphore(info)?;
                return result;
            } else {
                release_eeprom_semaphore(info)?;
                wait_millisec(5);
            }
        }

        // If time expired clear the bits holding the lock and retry
        if gssr & (fwmask | swmask) != 0 {
            self.mac_release_swfw_sync(info, gssr & (fwmask | swmask))?;
        }

        wait_millisec(5);
        Err(SwfwSync)
    }

    /// mac_release_swhw_sync() For X540 ixgbe_release_swfw_sync_X540()
    fn mac_release_swfw_sync(&self, info: &PCIeInfo, mask: u32) -> Result<(), IxgbeDriverErr> {
        let mut gssr;
        let swmask = mask;

        get_eeprom_semaphore(info)?;

        gssr = ixgbe_hw::read_reg(info, IXGBE_GSSR)?;
        gssr &= !swmask;
        ixgbe_hw::write_reg(info, IXGBE_GSSR, gssr)?;

        release_eeprom_semaphore(info)?;

        Ok(())
    }

    /// mac_get_bus_info - Generic set PCI bus info
    /// Gets the PCI bus info (speed, width, type) then calls helper function to
    /// store this data within the ixgbe_hw structure.
    fn mac_get_bus_info(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IxgbeHw,
    ) -> Result<IxgbeBusInfo, IxgbeDriverErr> {
        let Some(cap) = info.get_pcie_cap_mut() else {
            return Err(NotPciExpress);
        };
        let val = cap.get_link_status_control();
        let link_status = (val.bits() >> 16) as u16;

        set_pci_config_data(self, info, hw, link_status)
    }

    fn mac_enable_rx(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;
        let rxctrl = ixgbe_hw::read_reg(info, IXGBE_RXCTRL)?;
        ixgbe_hw::write_reg(info, IXGBE_RXCTRL, rxctrl | IXGBE_RXCTRL_RXEN)?;
        if hw.mac.mac_type != IxgbeMac82598EB && hw.mac.set_lben {
            let mut pfdtxgswc = ixgbe_hw::read_reg(info, IXGBE_PFDTXGSWC)?;
            pfdtxgswc |= IXGBE_PFDTXGSWC_VT_LBEN;
            ixgbe_hw::write_reg(info, IXGBE_PFDTXGSWC, pfdtxgswc)?;
            hw.mac.set_lben = false;
        }
        Ok(())
    }
    fn mac_disable_rx(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;
        let mut rxctrl = ixgbe_hw::read_reg(info, IXGBE_RXCTRL)?;
        if rxctrl & IXGBE_RXCTRL_RXEN != 0 {
            if hw.mac.mac_type != IxgbeMac82598EB {
                let mut pfdtxgswc = ixgbe_hw::read_reg(info, IXGBE_PFDTXGSWC)?;
                if pfdtxgswc & IXGBE_PFDTXGSWC_VT_LBEN != 0 {
                    pfdtxgswc &= !IXGBE_PFDTXGSWC_VT_LBEN;
                    ixgbe_hw::write_reg(info, IXGBE_PFDTXGSWC, pfdtxgswc)?;
                    hw.mac.set_lben = true;
                } else {
                    hw.mac.set_lben = false;
                }
            }
            rxctrl &= !IXGBE_RXCTRL_RXEN;
            ixgbe_hw::write_reg(info, IXGBE_RXCTRL, rxctrl)?;
        }
        Ok(())
    }
    fn mac_enable_rx_dma(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
        regval: u32,
    ) -> Result<(), IxgbeDriverErr> {
        if regval & IXGBE_RXCTRL_RXEN != 0 {
            self.mac_enable_rx(info, hw)?;
        } else {
            self.mac_disable_rx(info, hw)?;
        }
        Ok(())
    }

    fn mac_get_link_capabilities(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
    ) -> Result<(u32, bool), IxgbeDriverErr>;

    fn mac_setup_link(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
        speed: u32,
        autoneg_wait_to_complete: bool,
    ) -> Result<(), IxgbeDriverErr>;

    fn mac_setup_mac_link(
        &self,
        _info: &PCIeInfo,
        _hw: &mut IxgbeHw,
        _speed: u32,
        _autoneg_wait_to_complete: bool,
    ) -> Result<(), IxgbeDriverErr> {
        log::error!("mac_setup_sfp: Not Implemented");
        Ok(())
    }

    fn mac_setup_sfp(&self, _info: &PCIeInfo, _hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        log::error!("mac_setup_sfp: Not Implemented");
        Ok(())
    }

    fn mac_set_rate_select_speed(
        &self,
        _info: &PCIeInfo,
        _hw: &mut IxgbeHw,
        _speed: u32,
    ) -> Result<(), IxgbeDriverErr> {
        log::error!("mac_setup_sfp: Not Implemented");
        Ok(())
    }

    // PHY Operations

    fn phy_init(&self, _info: &PCIeInfo, _hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        log::error!("phy_init: Not implemented");
        Ok(())
    }

    /// phy_reset - Performs a PHY reset
    fn phy_reset(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        use PhyType::*;

        if hw.phy.phy_type == IxgbePhyUnknown {
            phy_identify_phy_generic(self, info, hw)?;
        }

        if hw.phy.phy_type == IxgbePhyNone {
            return Ok(());
        }

        // Don't reset PHY if it's shut down due to overtemp.
        if Err(IxgbeDriverErr::Overtemp) == self.phy_check_overtemp(info, hw) {
            return Ok(());
        }

        // Blocked by MNG FW so bail
        if check_reset_blocked(info, hw)? {
            return Ok(());
        }

        // Perform soft PHY reset to the PHY_XS.
        // This will cause a soft reset to the PHY
        self.phy_write_reg(
            info,
            hw,
            IXGBE_MDIO_PHY_XS_CONTROL,
            IXGBE_MDIO_PHY_XS_DEV_TYPE,
            IXGBE_MDIO_PHY_XS_RESET,
        )?;

        // Poll for reset bit to self-clear indicating reset is complete.
        // Some PHYs could take up to 3 seconds to complete and need about
        // 1.7 usec delay after the reset is complete.
        let mut ctrl = 0;
        for _ in 0..30 {
            wait_millisec(100);
            if hw.phy.phy_type == IxgbePhyX550emExtT {
                ctrl = self.phy_read_reg(
                    info,
                    hw,
                    IXGBE_MDIO_TX_VENDOR_ALARMS_3,
                    IXGBE_MDIO_PMA_PMD_DEV_TYPE,
                )?;

                if ctrl & IXGBE_MDIO_TX_VENDOR_ALARMS_3_RST_MASK != 0 {
                    wait_microsec(2);
                    break;
                }
            } else {
                ctrl = self.phy_read_reg(
                    info,
                    hw,
                    IXGBE_MDIO_PHY_XS_CONTROL,
                    IXGBE_MDIO_PHY_XS_DEV_TYPE,
                )?;

                if ctrl & IXGBE_MDIO_PHY_XS_RESET == 0 {
                    wait_microsec(2);
                    break;
                }
            }
        }

        if ctrl & IXGBE_MDIO_PHY_XS_RESET != 0 {
            log::error!("PHY reset polling failed to complete.\n");
            return Err(IxgbeDriverErr::ResetFailed);
        }

        Ok(())
    }

    fn phy_check_overtemp(&self, info: &PCIeInfo, hw: &IxgbeHw) -> Result<(), IxgbeDriverErr> {
        if info.get_id() != IXGBE_DEV_ID_82599_T3_LOM {
            return Ok(());
        }

        // Check that the LASI temp alarm status was triggered
        let phy_data = self.phy_read_reg(
            info,
            hw,
            IXGBE_TN_LASI_STATUS_REG,
            IXGBE_MDIO_PMA_PMD_DEV_TYPE,
        )?;

        if phy_data & IXGBE_TN_LASI_STATUS_TEMP_ALARM == 0 {
            return Ok(());
        }

        log::error!("Device over temperature");
        Err(IxgbeDriverErr::Overtemp)
    }

    #[allow(dead_code)]
    fn phy_setup_phy_link_tnx(&self) -> Result<(), IxgbeDriverErr> {
        log::error!("phy_setup_phy_link_tnx: Not implemented");
        Err(IxgbeDriverErr::NotImplemented)
    }

    #[allow(dead_code)]
    fn phy_check_phy_link_tnx(&self) -> Result<(), IxgbeDriverErr> {
        log::error!("phy_check_phy_link_tnx: Not implemented");
        Err(IxgbeDriverErr::NotImplemented)
    }

    #[allow(dead_code)]
    fn phy_get_phy_firmware_version_tnx(&self) -> Result<(), IxgbeDriverErr> {
        log::error!("phy_get_phy_firmware_version_tnx: Not implemented");
        Err(IxgbeDriverErr::NotImplemented)
    }

    fn phy_read_i2c_byte(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        byte_offset: u8,
        dev_addr: u8,
    ) -> Result<u8, IxgbeDriverErr> {
        read_i2c_byte_generic_int(self, info, hw, byte_offset, dev_addr, true)
    }

    fn phy_write_i2c_byte(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        byte_offset: u8,
        dev_addr: u8,
        data: u8,
    ) -> Result<(), IxgbeDriverErr> {
        write_i2c_byte_generic_int(self, info, hw, byte_offset, dev_addr, data, true)
    }

    fn phy_read_i2c_eeprom(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        byte_offset: u8,
    ) -> Result<u8, IxgbeDriverErr> {
        self.phy_read_i2c_byte(info, hw, byte_offset, IXGBE_I2C_EEPROM_DEV_ADDR)
    }

    #[allow(dead_code)]
    fn phy_write_i2c_eeprom(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        byte_offset: u8,
        eeprom_data: u8,
    ) -> Result<(), IxgbeDriverErr> {
        self.phy_write_i2c_byte(
            info,
            hw,
            byte_offset,
            IXGBE_I2C_EEPROM_DEV_ADDR,
            eeprom_data,
        )
    }

    /// phy_identify - Get physical layer module
    /// Determines the physical layer module found on the current adapter.
    fn phy_identify(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        phy_identify_phy_generic(self, info, hw)
    }

    fn phy_read_reg(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        reg_addr: u32,
        device_type: u32,
    ) -> Result<u16, IxgbeDriverErr> {
        let gssr = hw.phy.phy_semaphore_mask;

        mac_swfw_sync_mut(self, info, gssr, 0, || {
            self.phy_read_reg_mdi(info, hw, reg_addr, device_type)
        })
    }

    fn phy_write_reg(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        reg_addr: u32,
        device_type: u32,
        phy_data: u16,
    ) -> Result<(), IxgbeDriverErr> {
        let gssr = hw.phy.phy_semaphore_mask;

        mac_swfw_sync_mut(self, info, gssr, 0, || {
            self.phy_write_reg_mdi(info, hw, reg_addr, device_type, phy_data)
        })
    }

    fn phy_read_reg_mdi(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        reg_addr: u32,
        device_type: u32,
    ) -> Result<u16, IxgbeDriverErr> {
        let mut command: u32 = (reg_addr << IXGBE_MSCA_NP_ADDR_SHIFT)
            | (device_type << IXGBE_MSCA_DEV_TYPE_SHIFT)
            | (hw.phy.addr << IXGBE_MSCA_PHY_ADDR_SHIFT)
            | (IXGBE_MSCA_ADDR_CYCLE | IXGBE_MSCA_MDI_COMMAND) as u32;

        ixgbe_hw::write_reg(info, IXGBE_MSCA, command)?;

        command = check_address_cycle_complete(info)?;
        if (command & IXGBE_MSCA_MDI_COMMAND as u32) != 0 {
            log::error!("PHY address command did not complete");
            return Err(Phy);
        }

        command = (reg_addr << IXGBE_MSCA_NP_ADDR_SHIFT)
            | (device_type << IXGBE_MSCA_DEV_TYPE_SHIFT)
            | (hw.phy.addr << IXGBE_MSCA_PHY_ADDR_SHIFT)
            | (IXGBE_MSCA_READ | IXGBE_MSCA_MDI_COMMAND) as u32;

        ixgbe_hw::write_reg(info, IXGBE_MSCA, command)?;

        command = check_address_cycle_complete(info)?;
        if (command & IXGBE_MSCA_MDI_COMMAND as u32) != 0 {
            log::error!("PHY write command did not complete");
            return Err(Phy);
        }

        // Read operation is complete. Get the data from MSRWD
        let mut data = ixgbe_hw::read_reg(info, IXGBE_MSRWD)?;
        data >>= IXGBE_MSRWD_READ_DATA_SHIFT;

        Ok(data as u16)
    }

    fn phy_write_reg_mdi(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        reg_addr: u32,
        device_type: u32,
        phy_data: u16,
    ) -> Result<(), IxgbeDriverErr> {
        // Put the data in the MDI single read write data register
        ixgbe_hw::write_reg(info, IXGBE_MSRWD, phy_data as u32)?;

        let mut command = (reg_addr << IXGBE_MSCA_NP_ADDR_SHIFT)
            | (device_type << IXGBE_MSCA_DEV_TYPE_SHIFT)
            | (hw.phy.addr << IXGBE_MSCA_PHY_ADDR_SHIFT)
            | (IXGBE_MSCA_ADDR_CYCLE | IXGBE_MSCA_MDI_COMMAND) as u32;

        ixgbe_hw::write_reg(info, IXGBE_MSCA, command)?;

        command = check_address_cycle_complete(info)?;
        if (command & IXGBE_MSCA_MDI_COMMAND as u32) != 0 {
            log::error!("PHY address command did not complete");
            return Err(Phy);
        }

        command = (reg_addr << IXGBE_MSCA_NP_ADDR_SHIFT)
            | (device_type << IXGBE_MSCA_DEV_TYPE_SHIFT)
            | (hw.phy.addr << IXGBE_MSCA_PHY_ADDR_SHIFT)
            | (IXGBE_MSCA_WRITE | IXGBE_MSCA_MDI_COMMAND) as u32;

        ixgbe_hw::write_reg(info, IXGBE_MSCA, command)?;

        command = check_address_cycle_complete(info)?;
        if (command & IXGBE_MSCA_MDI_COMMAND as u32) != 0 {
            log::error!("PHY write command did not complete");
            return Err(Phy);
        }

        Ok(())
    }

    /// phy_set_power(&self, info: &PCIeInfo, hw: &IxgbeHw, on: bool) -> Result<(), IxgbeDriverErr>;
    fn phy_set_power(
        &self,
        _info: &PCIeInfo,
        _hw: &IxgbeHw,
        _on: bool,
    ) -> Result<(), IxgbeDriverErr> {
        log::debug!("phy_set_power() Not Implemented");
        Ok(())
    }

    /// phy_setup_link_speed - Sets the auto advertised capabilities
    fn phy_setup_link_speed(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
        speed: u32,
        _autoneg_wait_to_complete: bool,
    ) -> Result<(), IxgbeDriverErr> {
        // Clear autoneg_advertised and set new values based on input link
        // speed.
        hw.phy.autoneg_advertised = 0;

        if speed & IXGBE_LINK_SPEED_10GB_FULL != 0 {
            hw.phy.autoneg_advertised |= IXGBE_LINK_SPEED_10GB_FULL;
        }

        if speed & IXGBE_LINK_SPEED_5GB_FULL != 0 {
            hw.phy.autoneg_advertised |= IXGBE_LINK_SPEED_5GB_FULL;
        }

        if speed & IXGBE_LINK_SPEED_2_5GB_FULL != 0 {
            hw.phy.autoneg_advertised |= IXGBE_LINK_SPEED_2_5GB_FULL;
        }

        if speed & IXGBE_LINK_SPEED_1GB_FULL != 0 {
            hw.phy.autoneg_advertised |= IXGBE_LINK_SPEED_1GB_FULL;
        }

        if speed & IXGBE_LINK_SPEED_100_FULL != 0 {
            hw.phy.autoneg_advertised |= IXGBE_LINK_SPEED_100_FULL;
        }

        if speed & IXGBE_LINK_SPEED_10_FULL != 0 {
            hw.phy.autoneg_advertised |= IXGBE_LINK_SPEED_10_FULL;
        }

        // Setup link based on the new speed settings
        self.phy_setup_link(info, hw)?;

        Ok(())
    }

    /// phy_setup_link - Set and restart auto-neg
    /// Restart auto-negotiation and PHY and waits for completion.
    fn phy_setup_link(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        phy_setup_link_generic(self, info, hw)
    }

    fn phy_identify_sfp(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        phy_identify_module_generic(self, info, hw)
    }

    // EEPROM Operations

    fn eeprom_init_params(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
    ) -> Result<(), IxgbeDriverErr> {
        let eec_offset = get_eec_offset(info.get_id())?;
        log::trace!("eeprom_init_params");

        eeprom.eeprom_type = EepromType::IxgbeEepromNone;
        // Set default semaphore delay to 10ms which is a well tested value
        eeprom.semaphore_delay = 10;
        // Clear EEPROM page size, it will be initialized as needed
        eeprom.word_page_size = 0;

        // Check for EEPROM present first.
        // If not present leave as none
        let eec = ixgbe_hw::read_reg(info, eec_offset)?;
        if eec & IXGBE_EEC_PRES != 0 {
            eeprom.eeprom_type = EepromType::IxgbeEepromSpi;

            // SPI EEPROM is assumed here.  This code would need to
            // change if a future EEPROM is not SPI.
            let eeprom_size = (eec & IXGBE_EEC_SIZE) as u16 >> IXGBE_EEC_SIZE_SHIFT;
            eeprom.word_size = 1 << (eeprom_size + IXGBE_EEPROM_WORD_SIZE_SHIFT);
        }

        if eec & IXGBE_EEC_ADDR_SIZE != 0 {
            eeprom.address_bits = 16;
        } else {
            eeprom.address_bits = 8;
        }

        Ok(())
    }

    fn eeprom_read(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
        offset: u16,
        data: &mut [u16],
    ) -> Result<(), IxgbeDriverErr> {
        read_eerd_buffer_generic(self, info, eeprom, offset, 1, data)
    }

    ///  eeprom_validate_checksum - Validate EEPROM checksum
    ///  //  Performs checksum calculation and validates the EEPROM checksum.  If the
    ///  caller does not need checksum_val, the value can be NULL.
    fn eeprom_validate_checksum(&self, info: &PCIeInfo) -> Result<IxgbeEepromInfo, IxgbeDriverErr> {
        log::trace!("eeprom_validate_checksum");

        let mut eeprom = IxgbeEepromInfo {
            eeprom_type: EepromType::IxgbeEepromUninitialized,
            semaphore_delay: 0,
            word_size: 0,
            address_bits: 0,
            word_page_size: 0,
            ctrl_word_3: 0,
        };

        //  Read the first word from the EEPROM. If this times out or fails, do
        // not continue or we could be in for a very long wait while every
        // EEPROM read fails
        let mut data = [0; 1];
        if let Err(e) = self.eeprom_read(info, &mut eeprom, 0, &mut data) {
            log::debug!("EEPROM read failed\n");
            return Err(e);
        }

        let checksum = self.eeprom_calc_checksum(info, &mut eeprom)?;

        let mut read_checksum = [0; 1];
        if let Err(e) =
            self.eeprom_read(info, &mut eeprom, IXGBE_EEPROM_CHECKSUM, &mut read_checksum)
        {
            log::debug!("EEPROM read failed\n");
            return Err(e);
        }

        //  Verify read checksum from EEPROM is the same as
        // calculated checksum
        if read_checksum[0] != checksum {
            return Err(IxgbeDriverErr::EepromChecksum);
        }

        Ok(eeprom)
    }

    /// eeprom_calc_checksum - Calculates and returns the checksum
    /// Returns a negative error code on error, or the 16-bit checksum
    fn eeprom_calc_checksum(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
    ) -> Result<u16, IxgbeDriverErr> {
        let mut checksum = 0;
        // Include 0x0-0x3F in the checksum
        for i in 0..IXGBE_EEPROM_CHECKSUM {
            let mut word = [0; 1];
            if self.eeprom_read(info, eeprom, i, &mut word).is_err() {
                log::debug!("EEPROM read failed\n");
                return Err(IxgbeDriverErr::Eeprom);
            }
            checksum += word[0];
        }

        // Include all data from pointers except for the fw pointer
        for i in IXGBE_PCIE_ANALOG_PTR..IXGBE_FW_PTR {
            let mut pointer = [0; 1];
            if self.eeprom_read(info, eeprom, i, &mut pointer).is_err() {
                log::debug!("EEPROM read failed\n");
                return Err(IxgbeDriverErr::Eeprom);
            }

            // If the pointer seems invalid
            if pointer[0] == 0xFFFF || pointer[0] == 0 {
                continue;
            }

            let mut length = [0; 1];
            if self
                .eeprom_read(info, eeprom, pointer[0], &mut length)
                .is_err()
            {
                log::debug!("EEPROM read failed\n");
                return Err(IxgbeDriverErr::Eeprom);
            }

            if length[0] == 0xFFFF || length[0] == 0 {
                continue;
            }

            let mut word = [0; 1];
            for j in pointer[0] + 1..=pointer[0] + length[0] {
                if self.eeprom_read(info, eeprom, j, &mut word).is_err() {
                    log::debug!("EEPROM read failed\n");
                    return Err(IxgbeDriverErr::Eeprom);
                }
                checksum += word[0];
            }
        }

        checksum = IXGBE_EEPROM_SUM - checksum;

        Ok(checksum)
    }

    fn mac_enable_tx_laser(
        &self,
        _info: &PCIeInfo,
        _hw: &mut IxgbeHw,
    ) -> Result<(), IxgbeDriverErr> {
        Ok(())
    }
}
