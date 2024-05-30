use core::fmt::Arguments;

use super::{
    ixgbe_hw::{self, IxgbeEepromInfo, IxgbeBusInfo,},
    ixgbe_regs::*,
    Ixgbe,
    IxgbeDriverErr::{self, *},
};
use crate::pcie::{capability::pcie_cap::PCIeCap, PCIeInfo};
use awkernel_lib::delay::wait_microsec;
use ixgbe_hw::{IxgbeHw, MacType, EepromType, MediaType, FcMode};

// clear_tx_pending - Clear pending TX work from the PCIe fifo
// The 82599 and x540 MACs can experience issues if TX work is still pending
// when a reset occurs.  This function prevents this by flushing the PCIe
// buffers on the system.
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
    wait_microsec(3);

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

    /* initiate cleaning flow for buffers in the PCIe transaction layer */
    let gcr_ext = ixgbe_hw::read_reg(info, IXGBE_GCR_EXT)?;
    ixgbe_hw::write_reg(
        info,
        IXGBE_GCR_EXT,
        gcr_ext | IXGBE_GCR_EXT_BUFFERS_CLEAR as u32,
    )?;

    /* Flush all writes and allow 20usec for all transactions to clear */
    ixgbe_hw::write_flush(info)?;
    wait_microsec(20);

    /* restore previous register values */
    ixgbe_hw::write_reg(info, IXGBE_GCR_EXT, gcr_ext)?;
    ixgbe_hw::write_reg(info, IXGBE_HLREG0, hlreg0)?;
    Ok(())
}

// MAC Helper Functions

 // start_hw_generic - Prepare hardware for Tx/Rx
 // Starts the hardware by filling the bus info structure and media type, clears
 // all on chip counters, initializes receive address registers, multicast
 // table, VLAN filter table, calls routine to set up link and flow control
 // settings, and leaves transmit and receive units disabled and uninitialized
pub fn start_hw_generic<T: IxgbeOperations + ?Sized>(ops: &T,info: &PCIeInfo, hw: &mut IxgbeHw)->Result<(), IxgbeDriverErr>{
    use ixgbe_hw::MacType::*;
	/* Set the media type */
	hw.phy.media_type = ops.mac_get_media_type();

	/* PHY ops initialization must be done in reset_hw() */

	/* Clear the VLAN filter table */
	ops.mac_clear_vfta(info, hw);

	/* Clear statistics registers */
	ops.mac_clear_hw_cntrs(info, hw);

	/* Set No Snoop Disable */
	let mut ctrl_ext = ixgbe_hw::read_reg(info, IXGBE_CTRL_EXT)?;
	ctrl_ext |= IXGBE_CTRL_EXT_NS_DIS;
	ixgbe_hw::write_reg(info, IXGBE_CTRL_EXT, ctrl_ext)?;
	ixgbe_hw::write_flush(info);

	// Setup flow control 
    ops.mac_setup_fc(info,hw)?;

	// Cache bit indicating need for crosstalk fix 
	let crosstalk_fix = match hw.mac.mac_type {
	IxgbeMac82599EB |IxgbeMacX550EMX | IxgbeMacX550EMA => {
		let device_caps = ops.mac_get_device_caps(info)?;
		if device_caps & IXGBE_DEVICE_CAPS_NO_CROSSTALK_WR != 0 {
			false
        } else {
			true
        }
    },
	_ => 
		false
	};

    hw.crosstalk_fix = crosstalk_fix;

	/* Clear adapter stopped flag */
	hw.adapter_stopped = false;

    Ok(())
}

 // start_hw_gen2 - Init sequence for common device family
 // Performs the init sequence common to the second generation
 // of 10 GbE devices.
 // Devices in the second generation:
 //    82599
 //    X540
pub fn start_hw_gen2(info: &PCIeInfo, hw: &IxgbeHw)-> Result<(), IxgbeDriverErr>{
	/* Clear the rate limiters */
    for i in 0..hw.mac.max_tx_queues {
		ixgbe_hw::write_reg(info, IXGBE_RTTDQSEL, i)?;
		ixgbe_hw::write_reg(info, IXGBE_RTTBCNRC, 0)?;
	}
	ixgbe_hw::write_flush(info);

	/* Disable relaxed ordering */
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

// validate_mac_addr - Validate MAC address
// Tests a MAC address to ensure it is a valid Individual Address
fn validate_mac_addr(mac_addr: &[u8]) -> Result<(), IxgbeDriverErr> {
    /* Make sure it is not a multicast address */
    let status = if ixgbe_is_multicast(mac_addr) {
        Err(InvalidMacAddr)
    /* Not a broadcast address */
    } else if ixgbe_is_broadcast(mac_addr) {
        Err(InvalidMacAddr)
    /* Reject the zero address */
    } else if mac_addr[0] == 0
        && mac_addr[1] == 0
        && mac_addr[2] == 0
        && mac_addr[3] == 0
        && mac_addr[4] == 0
        && mac_addr[5] == 0
    {
        Err(InvalidMacAddr)
    } else {
        Ok(())
    };

    status
}

// pcie_timeout_poll - Return number of times to poll for completion
// System-wide timeout range is encoded in PCIe Device Control2 register.
// Add 10% to specified maximum and return the number of times to poll for
// completion timeout, in units of 100 microsec.  Never return less than
// 800 = 80 millisec.
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

// disable_pcie_master - Disable PCI-express master access
// Disables PCI-Express master access and verifies there are no pending
// requests. IXGBE_ERR_MASTER_REQUESTS_PENDING is returned if master disable
// bit hasn't caused the master requests to be disabled, else IXGBE_SUCCESS
// is returned signifying master requests disabled.
fn disable_pcie_master(info: &mut PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
    use crate::pcie::capability::pcie_cap::registers::DeviceStatusControl;
    // Always set this bit to ensure any future transactions are blocked
    ixgbe_hw::write_reg(info, IXGBE_CTRL, IXGBE_CTRL_GIO_DIS as u32)?;

    // Exit if master requests are blocked
    let mut status = ixgbe_hw::read_reg(info, IXGBE_STATUS)?;
    if status & IXGBE_STATUS_GIO == 0 {
        return Ok(());
    }

    /* Poll for master request bit to clear */
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

 // set_pci_config_data - Generic store PCI bus info
 // Stores the PCI bus info (speed, width, type) within the ixgbe_hw structure
fn set_pci_config_data<T: IxgbeOperations + ?Sized>(ops: &T, info: &PCIeInfo, hw: &mut IxgbeHw, link_status: u16)->Result<IxgbeBusInfo,IxgbeDriverErr>{
    use ixgbe_hw::{BusType::*, BusSpeed::*, BusWidth::*};

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

	let speed =  match link_status as u32 & IXGBE_PCI_LINK_SPEED {
	IXGBE_PCI_LINK_SPEED_2500 => IxgbeBusSpeed2500,
	IXGBE_PCI_LINK_SPEED_5000 => IxgbeBusSpeed5000,
	IXGBE_PCI_LINK_SPEED_8000 => IxgbeBusSpeed8000,
	_ => IxgbeBusSpeedUnknown,
	};

	let (func, lan_id, instance_id) = ops.mac_set_lan_id_multi_port_pcie(info, hw)?;
    let businfo = IxgbeBusInfo { speed, width, bus_type, func, lan_id, instance_id };

    Ok(businfo)
}

 // device_supports_autoneg_fc - Check if device supports autonegotiation
 // This function returns TRUE if the device supports flow control
 // autonegotiation, and FALSE if it does not.
fn device_supports_autoneg_fc<T: IxgbeOperations + ?Sized>(ops: &T, info: &PCIeInfo, hw: &IxgbeHw) -> Result<bool,IxgbeDriverErr>{
    use ixgbe_hw::MediaType::*;

	let supported = match hw.phy.media_type {
    IxgbeMediaTypeFiberFixed | IxgbeMediaTypeFiberQsfp | IxgbeMediaTypeFiber => {
		/* flow control autoneg black list */
		match info.id {
		IXGBE_DEV_ID_X550EM_A_SFP | IXGBE_DEV_ID_X550EM_A_SFP_N | IXGBE_DEV_ID_X550EM_A_QSFP | IXGBE_DEV_ID_X550EM_A_QSFP_N =>
			false,
		_ => {
            let (speed, link_up) = ops.mac_check_link(info, hw, false)?;
            if link_up {
                if speed == IXGBE_LINK_SPEED_1GB_FULL{
                    true
                }else{
                    false
                }
            }else{
                true
            }
        }
        }
    }
	IxgbeMediaTypeBackplane => {
		if info.id == IXGBE_DEV_ID_X550EM_X_XFI {
            false
        } else {
            true
        }
    },
	IxgbeMediaTypeCopper => {
		/* only some copper devices support flow control autoneg */
		match info.id {
		IXGBE_DEV_ID_82599_T3_LOM | IXGBE_DEV_ID_X540T | IXGBE_DEV_ID_X540T1 | IXGBE_DEV_ID_X540_BYPASS | IXGBE_DEV_ID_X550T | IXGBE_DEV_ID_X550T1 |
IXGBE_DEV_ID_X550EM_X_10G_T | IXGBE_DEV_ID_X550EM_A_10G_T | IXGBE_DEV_ID_X550EM_A_1G_T | IXGBE_DEV_ID_X550EM_A_1G_T_L => true,
		_ => false,
		}
    },
    _ => false,
	};

	if !supported {
		log::error!("Device {:?} does not support flow control autoneg", info.id);
	}

    Ok(supported)
}

fn need_crosstalk_fix<T: IxgbeOperations + ?Sized >(ops: &T, hw: &IxgbeHw) -> bool {
    use ixgbe_hw::MediaType::*;
	/* Does FW say we need the fix */
	if !hw.crosstalk_fix {
		return false;
    }

	/* Only consider SFP+ PHYs i.e. media type fiber */
	match ops.mac_get_media_type() {
	IxgbeMediaTypeFiber | IxgbeMediaTypeFiberQsfp => true,
	_ =>  false,
    }
}

fn fc_autoneg_fiber(info: &PCIeInfo, hw:&mut IxgbeHw)->Result<(), IxgbeDriverErr>{
	// On multispeed fiber at 1g, bail out if
	// - link is up but AN did not complete, or if
	// - link is up and AN completed but timed out
    let linkstat = ixgbe_hw::read_reg(info, IXGBE_PCS1GLSTA)?;
    if (linkstat & IXGBE_PCS1GLSTA_AN_COMPLETE == 0) || (linkstat & IXGBE_PCS1GLSTA_AN_TIMED_OUT != 0) {
        log::debug!("Auto-Negotiation did not complete or timed out");
        return Err(FcNotNegotiated);
    }

	let pcs_anadv_reg = ixgbe_hw::read_reg(info, IXGBE_PCS1GANA)?;
	let pcs_lpab_reg = ixgbe_hw::read_reg(info, IXGBE_PCS1GANLP)?;


	negotiate_fc(hw, pcs_anadv_reg, pcs_lpab_reg, IXGBE_PCS1GANA_SYM_PAUSE,IXGBE_PCS1GANA_ASM_PAUSE, IXGBE_PCS1GANA_SYM_PAUSE, IXGBE_PCS1GANA_ASM_PAUSE)
}

 // fc_autoneg_backplane - Enable flow control IEEE clause 37
 // Enable flow control according to IEEE clause 37.
fn fc_autoneg_backplane(info:&PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr>{
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

	negotiate_fc(hw, autoc_reg, anlp1_reg, IXGBE_AUTOC_SYM_PAUSE, IXGBE_AUTOC_ASM_PAUSE, IXGBE_ANLP1_SYM_PAUSE, IXGBE_ANLP1_ASM_PAUSE)

}

// fc_autoneg_copper - Enable flow control IEEE clause 37
// Enable flow control according to IEEE clause 37.
fn fc_autoneg_copper<T: IxgbeOperations + ?Sized>(ops:&T, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr>{

	let technology_ability_reg = ops.phy_read_reg(info, hw, IXGBE_MDIO_AUTO_NEG_ADVT, IXGBE_MDIO_AUTO_NEG_DEV_TYPE)?;
	let lp_technology_ability_reg = ops.phy_read_reg(info, hw, IXGBE_MDIO_AUTO_NEG_LP, IXGBE_MDIO_AUTO_NEG_DEV_TYPE)?;

	negotiate_fc(hw, technology_ability_reg as u32, lp_technology_ability_reg as u32, IXGBE_TAF_SYM_PAUSE, IXGBE_TAF_ASM_PAUSE, IXGBE_TAF_SYM_PAUSE, IXGBE_TAF_ASM_PAUSE)
}

// negotiate_fc - Negotiate flow control
// Find the intersection between advertised settings and link partner's
// advertised settings
fn negotiate_fc(hw: &mut IxgbeHw, adv_reg: u32, lp_reg: u32, adv_sym :u32, adv_asm: u32, lp_sym: u32, lp_asm: u32) -> Result<(), IxgbeDriverErr>{
    use ixgbe_hw::FcMode::*;
    
	if (adv_reg == 0) ||  (lp_reg == 0) {
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
	} else if (adv_reg & adv_sym == 0) && (adv_reg & adv_asm != 0) && (lp_reg & lp_sym != 0) && (lp_reg & lp_asm != 0) {
		hw.fc.current_mode = IxgbeFcTxPause;
		log::debug!("Flow Control = TX PAUSE frames only.");
	} else if (adv_reg & adv_sym != 0) && (adv_reg & adv_asm != 0) && (lp_reg & lp_sym == 0) && (lp_reg & lp_asm != 0) {
		hw.fc.current_mode = IxgbeFcRxPause;
		log::debug!("Flow Control = RX PAUSE frames only.");
	} else {
		hw.fc.current_mode = IxgbeFcNone;
		log::debug!("Flow Control = NONE.");
	}
    Ok(())
}

// set_mta - Set bit-vector in multicast table
// // Sets the bit-vector in the multicast table.
pub fn set_mta(hw: &mut IxgbeHw, mc_addr: &[u8]){
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
    hw.mac.mta_shadow[vector_reg as usize] |= 1 << vector_bit;
    ()
}

// mta_vector - Determines bit-vector in multicast table to set
// // Extracts the 12 bits, from a multicast address, to determine which
// bit-vector to set in the multicast table. The hardware uses 12 bits, from
// incoming rx multicast addresses, to determine the bit-vector to check in
// the MTA. Which of the 4 combination, of 12-bits, the hardware uses is set
// by the MO field of the MCSTCTRL. The MO field is set during initialization
// to mc_filter_type.
pub fn mta_vector(hw: &IxgbeHw, mc_addr: &[u8]) -> u16 {
	let mut vector = match hw.mac.mc_filter_type {
	    0 => {
        // use bits [47:36] of the address
		    (mc_addr[4] >> 4) as u16 | ((mc_addr[5] as u16) << 4)
        },
	    1 => {
        // use bits [46:35] of the address
		    (mc_addr[4] >> 3) as u16 | ((mc_addr[5] as u16) << 5)
        },
	    2 => {
        // use bits [45:34] of the address
		    (mc_addr[4] >> 2) as u16 | ((mc_addr[5] as u16) << 6)
        },
	    3 => {
        // use bits [43:32] of the address 
		    (mc_addr[4]) as u16 | ((mc_addr[5] as u16) << 8)
        },
	    _ => {
        // Invalid mc_filter_type
		    log::debug!("MC filter type param set incorrectly\n");
		    panic!("incorrect multicast filter type");
	    },
    };

	// vector can only be 12-bits or boundary will be exceeded
	vector &= 0xFFF;
	vector
}

// get_copper_link_capabilities - Determines link capabilities
fn get_copper_link_capabilities<T: IxgbeOperations + ?Sized>(ops: &T, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(u32,bool), IxgbeDriverErr>{

    if hw.phy.speeds_supported == IXGBE_LINK_SPEED_UNKNOWN {
        get_copper_speeds_supported(ops, info, hw)?;
    }

    let speed = hw.phy.speeds_supported;

    Ok((speed, true))
}

// get_copper_speeds_supported - Get copper link speeds from phy
// Determines the supported link capabilities by reading the PHY auto
// negotiation register.
fn get_copper_speeds_supported<T: IxgbeOperations + ?Sized>(ops: &T, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr>{
    use ixgbe_hw::MacType::*;

	let speed_ability = ops.phy_read_reg(info, hw, IXGBE_MDIO_PHY_SPEED_ABILITY,
				      IXGBE_MDIO_PMA_PMD_DEV_TYPE)?;

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
	IxgbeMacX550EMX | IxgbeMacX550EMA => 
		hw.phy.speeds_supported &= !IXGBE_LINK_SPEED_100_FULL,
    _ => (),

	}

    Ok(())
}


 // probe_phy - Probe a single address for a PHY
 // Returns TRUE if PHY found
fn probe_phy<T: IxgbeOperations + ?Sized>(ops:&T, info: &PCIeInfo, hw: &mut IxgbeHw , phy_addr: u16) -> Result<(), IxgbeDriverErr>{
    use ixgbe_hw::PhyType::*;
	validate_phy_addr(ops, info, hw, phy_addr as u32)?;

	get_phy_id(ops, info, hw)?;

	hw.phy.phy_type = get_phy_type_from_id(hw.phy.id);

	if hw.phy.phy_type == IxgbePhyUnknown {
		let ext_ability = ops.phy_read_reg(info, hw, IXGBE_MDIO_PHY_EXT_ABILITY, IXGBE_MDIO_PMA_PMD_DEV_TYPE)?;
		if (ext_ability as u32 & (IXGBE_MDIO_PHY_10GBASET_ABILITY | IXGBE_MDIO_PHY_1000BASET_ABILITY)) != 0 {
			hw.phy.phy_type = IxgbePhyCuUnknown;
             }
		else{
			hw.phy.phy_type = IxgbePhyGeneric;
        }
	}

    Ok(())
}

//  validate_phy_addr - Determines phy address is valid
fn validate_phy_addr<T: IxgbeOperations + ?Sized>(ops:&T, info:&PCIeInfo, hw: &mut IxgbeHw, phy_addr: u32) -> Result<(), IxgbeDriverErr>{
	hw.phy.addr = phy_addr;
	let phy_id = ops.phy_read_reg(info, hw, IXGBE_MDIO_PHY_ID_HIGH, IXGBE_MDIO_PMA_PMD_DEV_TYPE)?;

	if phy_id != 0xFFFF && phy_id != 0x0 {
        return Ok(());
    }

	return Err(PhyAddrInvalid);
}

//  get_phy_id - Get the phy type
fn get_phy_id<T: IxgbeOperations + ?Sized >(ops: &T, info: &PCIeInfo, hw: &mut IxgbeHw)->Result<(), IxgbeDriverErr>{
	let phy_id_high = ops.phy_read_reg(info, hw, IXGBE_MDIO_PHY_ID_HIGH,
				      IXGBE_MDIO_PMA_PMD_DEV_TYPE)?;

	hw.phy.id = (phy_id_high as u32) << 16;
	let phy_id_low = ops.phy_read_reg(info, hw, IXGBE_MDIO_PHY_ID_LOW, IXGBE_MDIO_PMA_PMD_DEV_TYPE)?;

	hw.phy.id |= phy_id_low as u32 & IXGBE_PHY_REVISION_MASK;
	hw.phy.revision = phy_id_low as u32 & !IXGBE_PHY_REVISION_MASK;
    Ok(())
}

// get_phy_type_from_id - Get the phy type
fn get_phy_type_from_id(phy_id: u32) -> ixgbe_hw::PhyType
{
    use ixgbe_hw::PhyType::*;

	let phy_type = match phy_id {
	TN1010_PHY_ID => IxgbePhyTn,
	X550_PHY_ID2 | X550_PHY_ID3 | X540_PHY_ID => IxgbePhyAq,
	QT2022_PHY_ID => IxgbePhyQt,
    ATH_PHY_ID => IxgbePhyNl,
	X557_PHY_ID | X557_PHY_ID2 => IxgbePhyX550emExtT,
	IXGBE_M88E1500_E_PHY_ID | IXGBE_M88E1543_E_PHY_ID => IxgbePhyExt1gT,
	_ => IxgbePhyUnknown,
	};

    phy_type
}


// Eeprom Helper Functions
fn poll_eerd_eewr_done(info: &PCIeInfo, ee_reg: u32) -> Result<(), IxgbeDriverErr> {
    let mut reg;
    let mut stopped_i = 0;

    for i in 0..IXGBE_EERD_EEWR_ATTEMPTS {
        if ee_reg == IXGBE_NVM_POLL_READ as u32 {
            reg = ixgbe_hw::read_reg(info, IXGBE_EERD)?;
        } else {
            reg = ixgbe_hw::read_reg(info, IXGBE_EEWR)?;
        }
        if reg & IXGBE_EEPROM_RW_REG_DONE as u32 != 0 {
            stopped_i = i;
            break;
        }
        wait_microsec(5);
    }

    if stopped_i == IXGBE_EERD_EEWR_ATTEMPTS {
        log::info!("EEPROM read/write done polling timed out");
        return Err(Eeprom);
    }

    Ok(())
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
        (eeprom.eeprom_type, eeprom.semaphore_delay, eeprom.word_size) = ops.init_params(info)?;
    }

    if words == 0 {
        log::info!("Invalid EEPROM words");
        return Err(IxgbeDriverErr::InvalidArgument);
    }

    if words as usize != data.len() {
        log::info!("EEPROM words doesn't match the size of the buffer");
        return Err(IxgbeDriverErr::InvalidArgument);
    }

    if offset >= eeprom.word_size {
        log::info!("Invalid EEPROM offset");
        return Err(IxgbeDriverErr::Eeprom);
    }

    for i in 0..words {
        eerd = ((offset + i) << IXGBE_EEPROM_RW_ADDR_SHIFT) | IXGBE_EEPROM_RW_REG_START;

        ixgbe_hw::write_reg(info, IXGBE_EERD, eerd as u32)?;
        poll_eerd_eewr_done(info, IXGBE_NVM_POLL_READ as u32)?;

        data[i as usize] =
            (ixgbe_hw::read_reg(info, IXGBE_EERD)? >> IXGBE_EEPROM_RW_REG_DATA) as u16;
    }
    for (i, d) in data.iter_mut().enumerate() {
        eerd = ((offset + i as u16) << IXGBE_EEPROM_RW_ADDR_SHIFT) | IXGBE_EEPROM_RW_REG_START;

        ixgbe_hw::write_reg(info, IXGBE_EERD, eerd as u32)?;
        poll_eerd_eewr_done(info, IXGBE_NVM_POLL_READ as u32)?;
        *d = (ixgbe_hw::read_reg(info, IXGBE_EERD)? >> IXGBE_EEPROM_RW_REG_DATA) as u16;
    }

    Ok(())
}

// Sets the hardware semaphores so EEPROM access can occur for bit-bang method
// TODO: Currently not available for X550EM_a: Should define IXGBE_BY_MAC to get the address for arbitrary NIC
fn get_eeprom_semaphore(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let timeout: u32 = 2000;
    let mut swsm;
    let mut status: Result<(), IxgbeDriverErr> = Err(Eeprom);
    let mut i = 0;

    // Get SMBI software semaphore between device drivers first
    while i < timeout {
        // If the SMBI bit is 0 when we read it, then the bit will be set and we have the semaphore
        swsm = ixgbe_hw::read_reg(info, IXGBE_SWSM)?;
        if !(swsm & IXGBE_SWSM_SMBI) != 0 {
            status = Ok(());
            break;
        }
        awkernel_lib::delay::wait_microsec(50);
        i += 1;
    }

    if i == timeout {
        release_eeprom_semaphore(info)?;

        awkernel_lib::delay::wait_microsec(50);

        // one last try
        swsm = ixgbe_hw::read_reg(info, IXGBE_SWSM)?;
        if !(swsm & IXGBE_SWSM_SMBI) != 0 {
            status = Ok(());
        }
    }

    // Get the semaphore between SW/FW
    if status.is_ok() {
        i = 0;
        while i < timeout {
            swsm = ixgbe_hw::read_reg(info, IXGBE_SWSM)?;

            // Set the SW EEPROM semaphore bit to request access
            swsm |= IXGBE_SWSM_SWESMBI;
            ixgbe_hw::write_reg(info, IXGBE_SWSM, swsm)?;

            // If we set the bit successfully then we got the semaphore.
            swsm = ixgbe_hw::read_reg(info, IXGBE_SWSM)?;
            if swsm & IXGBE_SWSM_SWESMBI != 0 {
                break;
            }

            awkernel_lib::delay::wait_microsec(50);
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

    return status;
}

// This function clears hardware semaphore bits.
fn release_eeprom_semaphore(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let mut swsm;

    swsm = ixgbe_hw::read_reg(info, IXGBE_SWSM)?;

    // Release both semaphores by writing 0 to the bits SWESMBI and SMBI
    swsm &= !(IXGBE_SWSM_SWESMBI | IXGBE_SWSM_SMBI);

    ixgbe_hw::write_reg(info, IXGBE_SWSM, swsm)?;
    ixgbe_hw::write_flush(info)
}

fn check_address_cycle_complete(info: &PCIeInfo) -> Result<u32, IxgbeDriverErr> {
    let mut command = 0;
    for _i in 0..IXGBE_MDIO_COMMAND_TIMEOUT {
        awkernel_lib::delay::wait_microsec(10);

        command = ixgbe_hw::read_reg(info, IXGBE_MSCA)?;
        if (command & IXGBE_MSCA_MDI_COMMAND as u32) == 0 {
            return Ok(command);
        }
    }

    Ok(command)
}

pub trait IxgbeOperations: Send {
    //fn get_self() -> Self;
    //fn new() -> Self;

    // MAC Operations
    fn mac_init_hw(&self, info: &mut PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        let ret = match self.mac_reset_hw(info, hw) {
            Ok(()) | Err(SfpNotPresent) => self.mac_start_hw(info, hw),
            Err(e) => Err(e),
        };

        ret
    }

    fn mac_reset_hw(&self, info: &mut PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        Ok(())
    }

    fn mac_start_hw(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr>;

    fn mac_get_media_type(&self)-> MediaType;

    // clear_vfta- Clear VLAN filter table
    // Clears the VLAN filer table, and the VMDq index associated with the filter
    fn mac_clear_vfta(&self, info: &PCIeInfo, hw: &IxgbeHw) -> Result<(), IxgbeDriverErr> {
        for offset in 0..hw.mac.vft_size {
            ixgbe_hw::write_reg(info, IXGBE_VFTA(offset as usize),0)?;
        }

        for offset in 0..IXGBE_VLVF_ENTRIES {
            ixgbe_hw::write_reg(info, IXGBE_VLVF(offset) as usize, 0)?;
            ixgbe_hw::write_reg(info, IXGBE_VLVFB(offset * 2) as usize, 0)?;
            ixgbe_hw::write_reg(info, IXGBE_VLVFB((offset * 2) + 1) as usize, 0)?;
        }

        Ok(())
    }

 // mac_clear_hw_cntrs - Generic clear hardware counters
 // Clears all hardware statistics counters by reading them from the hardware
 // Statistics counters are clear on read.
fn mac_clear_hw_cntrs(&self, info: &PCIeInfo, hw: &mut IxgbeHw)->Result<(),IxgbeDriverErr>{
    use ixgbe_hw::{MacType::*,read_reg};

	read_reg(info, IXGBE_CRCERRS)?;
	read_reg(info, IXGBE_ILLERRC)?;
	read_reg(info, IXGBE_ERRBC)?;
	read_reg(info, IXGBE_MSPDC)?;
	for i in 0..8 {
		read_reg(info, IXGBE_MPC(i));
    
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
	if hw.mac.mac_type >= IxgbeMac82599EB{
        for i in 0..8{
			read_reg(info, IXGBE_PXON2OFFCNT(i));
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
        for i in 0..8{
			read_reg(info, IXGBE_RNBC(i));
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
    for i in 0..16{
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
			let _ = self.identify_phy(info, hw);
        }
		self.phy_read_reg(info, hw, IXGBE_PCRC8ECL,
				     IXGBE_MDIO_PCS_DEV_TYPE)?;
		self.phy_read_reg(info, hw, IXGBE_PCRC8ECH,
				     IXGBE_MDIO_PCS_DEV_TYPE)?;
		self.phy_read_reg(info, hw, IXGBE_LDPCECL,
				     IXGBE_MDIO_PCS_DEV_TYPE)?;
		self.phy_read_reg(info, hw, IXGBE_LDPCECH,
				     IXGBE_MDIO_PCS_DEV_TYPE)?;
	}

    Ok(())
}

// identify_phy_generic - Get physical layer module
// Determines the physical layer module found on the current adapter.
fn identify_phy(&self, info: &PCIeInfo, hw: &mut IxgbeHw)-> Result<(), IxgbeDriverErr>{
    use ixgbe_hw::PhyType::*;

	if hw.phy.phy_semaphore_mask == 0 {
		if hw.bus.lan_id != 0{
			hw.phy.phy_semaphore_mask = IXGBE_GSSR_PHY1_SM;
        } else {
			hw.phy.phy_semaphore_mask = IXGBE_GSSR_PHY0_SM;
        }
	}

	if hw.phy.phy_type != IxgbePhyUnknown{
		return Ok(());
    }

	let phy_addr;
	if hw.phy.nw_mng_if_sel != 0 {
		phy_addr = (hw.phy.nw_mng_if_sel &
			    IXGBE_NW_MNG_IF_SEL_MDIO_PHY_ADD) >>
			   IXGBE_NW_MNG_IF_SEL_MDIO_PHY_ADD_SHIFT;
		return probe_phy(self, info, hw, phy_addr as u16);
	}

	let mut status = Err(PhyAddrInvalid);
    for phy_addr in 0..IXGBE_MAX_PHY_ADDR {
        match probe_phy(self, info, hw, phy_addr) {
            Ok(()) => {
                status = Ok(());
                break;
            }
            Err(_) => {continue;}
        }
	}

	//  Certain media types do not have a phy so an address will not
	// be found and the code will take this path.  Caller has to
	// decide if it is an error or not.
	if status != Ok(()){
		hw.phy.addr = 0;
    }

    status
}



    fn mac_get_mac_addr(&self, info: &PCIeInfo, mac_addr: &mut [u8]) -> Result<(), IxgbeDriverErr> {
        let rar_high = ixgbe_hw::read_reg(info, IXGBE_RAH(0) as usize)?;
        let rar_low = ixgbe_hw::read_reg(info, IXGBE_RAL(0) as usize)?;

        for i in 0..4 {
            mac_addr[i] = (rar_low >> (i * 8)) as u8;
        }
        for i in 0..2 {
            mac_addr[i + 4] = (rar_high >> (i * 8)) as u8;
        }

        Ok(())
    }

    // stop_adapter - Stop Tx/Rx units
    // Sets the adapter_stopped flag within ixgbe_hw struct. Clears interrupts,
    // disables transmit and receive units. The adapter_stopped flag is used by
    // the shared code and drivers to determine if the adapter is in a stopped
    // state and should not touch the hardware.
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

        /* flush all queues disables */
        ixgbe_hw::write_flush(info)?;
        wait_microsec(2);

        /*
         * Prevent the PCI-E bus from hanging by disabling PCI-E master
         * access and verify no pending requests
         */

        disable_pcie_master(info, hw)?;

        Ok(())
    }

    // mac_init_rx_addrs_generic - Initializes receive address filters.
    // Places the MAC address in receive address register 0 and clears the rest
    // of the receive address registers. Clears the multicast table. Assumes
    // the receiver is in reset when the routine is called.
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
                &mut hw.mac.addr,
                0,
                IXGBE_RAH_AV,
            )?;
        }

        // clear VMDq pool/queue selection for RAR 0
        self.mac_clear_vmdq(info, hw.mac.num_rar_entries, 0, IXGBE_CLEAR_VMDQ_ALL)?;

        hw.addr_ctrl.overflow_promisc = 0;
        hw.addr_ctrl.rar_used_count = 1;

        /* Zero out the other receive addresses. */
        for i in 0..hw.mac.num_rar_entries {
            ixgbe_hw::write_reg(info, IXGBE_RAL(i) as usize, 0)?;
            ixgbe_hw::write_reg(info, IXGBE_RAH(i) as usize, 0)?;
        }

        /* Clear the MTA */
        hw.addr_ctrl.mta_in_use = 0;
        ixgbe_hw::write_reg(info, IXGBE_MCSTCTRL, hw.mac.mc_filter_type as u32)?;

        for i in 0..hw.mac.mcft_size {
            ixgbe_hw::write_reg(info, IXGBE_MTA(i) as usize, 0)?;
        }

        self.mac_init_uta_tables(info)?;

        Ok(())
    }

    // ixgbe_clear_rar_generic - Remove Rx address register
    // Clears an ethernet address from a receive address register.
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

        /* clear VMDq pool/queue selection for this RAR */
        self.mac_clear_vmdq(info, num_rar_entries, index, IXGBE_CLEAR_VMDQ_ALL)?;

        Ok(())
    }

    // mac_set_rar_generic - Set Rx address register
    // Puts an ethernet address into a receive address register.
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

    // ixgbe_set_vmdq_generic - Associate a VMDq pool index with a rx address
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

    // ixgbe_clear_vmdq_generic - Disassociate a VMDq pool index from a rx address
    fn mac_clear_vmdq(
        &self,
        info: &PCIeInfo,
        num_rar_entries: u32,
        rar: u32,
        vmdq: u32,
    ) -> Result<(), IxgbeDriverErr> {
        /* Make sure we are using a valid rar index range */
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

    // ixgbe_init_uta_tables_generic - Initialize the Unicast Table Array
    fn mac_init_uta_tables(&self, info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
        for i in 0..128 {
            ixgbe_hw::write_reg(info, IXGBE_UTA(i), 0)?;
        }
        Ok(())
    }

    // setup_fc_generic - Set up flow control
    // Called at init time to set up flow control.
    fn mac_setup_fc(&self, info: &PCIeInfo, hw: &mut IxgbeHw)->Result<(),IxgbeDriverErr>{
        use ixgbe_hw::{FcMode::*, MediaType::*};
    /* Validate the requested mode */
	if hw.fc.strict_ieee && hw.fc.requested_mode == IxgbeFcRxPause {
        return Err(InvalidLinkSettings);
	}

	/*
	 * 10gig parts do not have a word in the EEPROM to determine the
	 * default flow control setting, so we explicitly set it to full.
	 */
	if hw.fc.requested_mode == IxgbeFcDefault{
		hw.fc.requested_mode = IxgbeFcFull;
    }

	/*
	 * Set up the 1G and 10G flow control advertisement registers so the
	 * HW will be able to do fc autoneg once the cable is plugged in.  If
	 * we link at 10G, the 1G advertisement is harmless and vice versa.
	 */
    let mut reg;
    let mut reg_bp;
    let mut reg_cu;
	(reg, reg_bp, reg_cu) = match hw.phy.media_type {
	IxgbeMediaTypeBackplane =>
		/* some MAC's need RMW protection on AUTOC */
		(0, self.mac_prot_autoc_read(info)?, 0),
		/* only backplane uses autoc so fall though */
	IxgbeMediaTypeFiberFixed | IxgbeMediaTypeFiberQsfp | IxgbeMediaTypeFiber =>
		(ixgbe_hw::read_reg(info, IXGBE_PCS1GANA)?, 0, 0),
	IxgbeMediaTypeCopper =>
		(0,0,self.phy_read_reg(info, hw, IXGBE_MDIO_AUTO_NEG_ADVT,
				     IXGBE_MDIO_AUTO_NEG_DEV_TYPE)? as u32),
	_ => (0,0,0),
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
		/* Flow control completely disabled by software override. */
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
		/*
		 * Tx Flow control is enabled, and Rx Flow control is
		 * disabled by software override.
		 */
		reg |= IXGBE_PCS1GANA_ASM_PAUSE;
		reg &= !IXGBE_PCS1GANA_SYM_PAUSE;
		match hw.phy.media_type {
        IxgbeMediaTypeBackplane =>
			(reg, (reg_bp | IXGBE_AUTOC_ASM_PAUSE) & IXGBE_AUTOC_SYM_PAUSE, reg_cu),
		IxgbeMediaTypeCopper =>
			(reg, reg_bp, (reg_cu | IXGBE_TAF_ASM_PAUSE) & !IXGBE_TAF_SYM_PAUSE),
        _ => (reg, reg_bp, reg_cu),
        }
    }
	IxgbeFcRxPause |
		/*
		 * Rx Flow control is enabled and Tx Flow control is
		 * disabled by software override. Since there really
		 * isn't a way to advertise that we are capable of RX
		 * Pause ONLY, we will advertise that we support both
		 * symmetric and asymmetric Rx PAUSE, as such we fall
		 * through to the fc_full statement.  Later, we will
		 * disable the adapter's ability to send PAUSE frames.
		 */
	IxgbeFcFull => {
		/* Flow control (both Rx and Tx) is enabled by SW override. */
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
		/*
		 * Enable auto-negotiation between the MAC & PHY;
		 * the MAC will advertise clause 37 flow control.
		 */
		ixgbe_hw::write_reg(info, IXGBE_PCS1GANA, reg)?;
		reg = ixgbe_hw::read_reg(info, IXGBE_PCS1GLCTL)?;

		/* Disable AN timeout */
		if hw.fc.strict_ieee {
			reg &= !IXGBE_PCS1GLCTL_AN_1G_TIMEOUT_EN;
        }

		ixgbe_hw::write_reg(info, IXGBE_PCS1GLCTL, reg)?;
	}

	/*
	 * AUTOC restart handles negotiation of 1G and 10G on backplane
	 * and copper. There is no need to set the PCS1GCTL register.
	 *
	 */
	if hw.phy.media_type == IxgbeMediaTypeBackplane {
		reg_bp |= IXGBE_AUTOC_AN_RESTART;
		self.mac_prot_autoc_write(info, reg_bp)?;
	} else if (hw.phy.media_type == IxgbeMediaTypeCopper) && device_supports_autoneg_fc(self,info, hw)? {
		self.phy_write_reg(info, hw, IXGBE_MDIO_AUTO_NEG_ADVT, IXGBE_MDIO_AUTO_NEG_DEV_TYPE, reg_cu as u16)?;
	}

    Ok(())
    }

 // fc_enable - Enable flow control
 // Enable flow control according to the current settings.
    fn mac_fc_enable(&self, info:&PCIeInfo, hw:&mut IxgbeHw) -> Result<(), IxgbeDriverErr>{
        use ixgbe_hw::FcMode::*;


        // Validate the water mark configuration 
        if hw.fc.pause_time == 0{
            return Err(InvalidLinkSettings);
        }

 	    // Low water mark of zero causes XOFF floods 
        for i in 0..IXGBE_DCB_MAX_TRAFFIC_CLASS {
            if (hw.fc.current_mode == IxgbeFcTxPause || hw.fc.current_mode == IxgbeFcFull) && (hw.fc.high_water[i] != 0 ){
                if (hw.fc.low_water[i] == 0) || (hw.fc.low_water[i] >= hw.fc.high_water[i]){
                    log::debug!("Invalid water mark configuration");
                    return Err(InvalidLinkSettings);
                }
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
	    IxgbeFcTxPause=> (mflcn_reg, fccfg_reg | IXGBE_FCCFG_TFCE_802_3X),
		// Flow control (both Rx and Tx) is enabled by SW override.
	    IxgbeFcFull => (mflcn_reg | IXGBE_MFLCN_RFCE, fccfg_reg | IXGBE_FCCFG_TFCE_802_3X),
        _ =>  {
		    log::error!( "Flow control param set incorrectly");
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
		    if (hw.fc.current_mode == IxgbeFcTxPause || hw.fc.current_mode == IxgbeFcFull) &&
		        hw.fc.high_water[i] != 0 {
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
        for i in 0..IXGBE_DCB_MAX_TRAFFIC_CLASS {
		    ixgbe_hw::write_reg(info, IXGBE_FCTTV(i), reg)?;
        }

	    // Configure flow control refresh threshold value 
	    ixgbe_hw::write_reg(info, IXGBE_FCRTV, hw.fc.pause_time as u32 / 2)?;

        Ok(())    
    }

    // fc_autoneg - Configure flow control
    // Compares our advertised flow control capabilities to those advertised by
    // our link partner, and determines the proper flow control mode to use.
    fn mac_fc_autoneg(&self, info: &PCIeInfo, hw: &mut IxgbeHw)->Result<(), IxgbeDriverErr>{
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
    	    /* Autoneg flow control on fiber adapters */
            IxgbeMediaTypeFiber | IxgbeMediaTypeFiberFixed | IxgbeMediaTypeFiberQsfp => {
                if speed == IXGBE_LINK_SPEED_1GB_FULL{
                    fc_autoneg_fiber(info, hw)?;
                } else {
                    return Err(FcNotNegotiated);
                }
            },
	        /* Autoneg flow control on backplane adapters */
            IxgbeMediaTypeBackplane => {
                fc_autoneg_backplane(info, hw)?;
            },
	        /* Autoneg flow control on copper adapters */
            IxgbeMediaTypeCopper => {
                if device_supports_autoneg_fc(self, info, hw)? {
                    fc_autoneg_copper(self, info, hw)?;
                }else{
                    return Err(FcNotNegotiated);
                }
            },
            _ => (),
        }

        hw.fc.fc_was_autonegged = true;

        Ok(())

    }

 // check_mink - Determine link and speed status
 // Reads the links register to determine if link is up and the current speed
fn mac_check_link(&self, info: &PCIeInfo, hw: &IxgbeHw, link_up_wait_to_complete:bool) -> Result<(u32, bool), IxgbeDriverErr>{
    use ixgbe_hw::MacType::*;

	/* If Crosstalk fix enabled do the sanity check of making sure
	 * the SFP+ cage is full.
	 */
	if need_crosstalk_fix(self, hw) {
		let sfp_cage_full = match hw.mac.mac_type {
		IxgbeMac82599EB =>
			ixgbe_hw::read_reg(info, IXGBE_ESDP)? & IXGBE_ESDP_SDP2,
		IxgbeMacX550EMX | IxgbeMacX550EMA =>
			ixgbe_hw::read_reg(info, IXGBE_ESDP)? & IXGBE_ESDP_SDP0,
		_ => 0, /* sanity check - No SFP+ devices here */
		};

		if sfp_cage_full == 0 {
            return Ok((IXGBE_LINK_SPEED_UNKNOWN, false));
		}
	}

	/* clear the old state */
	let links_orig = ixgbe_hw::read_reg(info, IXGBE_LINKS)?;

	let mut links_reg = ixgbe_hw::read_reg(info, IXGBE_LINKS)?;

	if links_orig != links_reg {
		log::debug!("LINKS changed from {:?} to {:?}\n",
			  links_orig, links_reg);
	}

    let mut link_up = false;
	if link_up_wait_to_complete {
        for _ in 0..hw.mac.max_link_up_time {
            if links_reg & IXGBE_LINKS_UP != 0 {
                link_up = true;
                break;
            }else{
                link_up = false;
            }
            wait_microsec(100);
            links_reg = ixgbe_hw::read_reg(info, IXGBE_LINKS)?;
        }
	} else {
		if links_reg & IXGBE_LINKS_UP != 0 {
		    link_up = true;
        } else{
			link_up = false;
        }
	}

    let speed = match links_reg & IXGBE_LINKS_SPEED_82599 {
	IXGBE_LINKS_SPEED_10G_82599 => {
		if hw.mac.mac_type >= IxgbeMacX550 && links_reg & IXGBE_LINKS_SPEED_NON_STD != 0{
            IXGBE_LINK_SPEED_2_5GB_FULL
        }else{
            IXGBE_LINK_SPEED_10GB_FULL
		}
    },
	IXGBE_LINKS_SPEED_1G_82599 => IXGBE_LINK_SPEED_1GB_FULL,
	IXGBE_LINKS_SPEED_100_82599 =>{
		if hw.mac.mac_type == IxgbeMacX550 && links_reg & IXGBE_LINKS_SPEED_NON_STD != 0 {
            IXGBE_LINK_SPEED_5GB_FULL
		}else{
            IXGBE_LINK_SPEED_100_FULL
        }
    },
	IXGBE_LINKS_SPEED_10_X550EM_A => {
		if info.id == IXGBE_DEV_ID_X550EM_A_1G_T || info.id == IXGBE_DEV_ID_X550EM_A_1G_T_L {
            IXGBE_LINK_SPEED_10_FULL
        } else {
            IXGBE_LINK_SPEED_UNKNOWN
        }
    },
	_ => IXGBE_LINK_SPEED_UNKNOWN
	};

    Ok((speed, link_up))
}


    fn mac_prot_autoc_read(&self, info: &PCIeInfo) -> Result<u32, IxgbeDriverErr>{
        ixgbe_hw::read_reg(info, IXGBE_AUTOC)
    }

    fn mac_prot_autoc_write(&self, info: &PCIeInfo, reg_val: u32) -> Result<(), IxgbeDriverErr>{
        ixgbe_hw::write_reg(info, IXGBE_AUTOC, reg_val)
    }

    fn mac_get_device_caps(&self, info: &PCIeInfo) ->Result<u32,IxgbeDriverErr>{
        ixgbe_hw::read_reg(info, IXGBE_DEVICE_CAPS)
    }

// set_lan_id_multi_port_pcie - Set LAN id for PCIe multiple port devices
// Determines the LAN function id by reading memory-mapped registers and swaps
// the port value if requested, and set MAC instance for devices that share
// CS4227.
// Doesn't suport X550EM_a currently
fn mac_set_lan_id_multi_port_pcie(&self, info: &PCIeInfo, hw: &mut IxgbeHw)->Result<(u16,u8,u16),IxgbeDriverErr>{

	let mut reg = ixgbe_hw::read_reg(info, IXGBE_STATUS)?;
	let mut func = ((reg & IXGBE_STATUS_LAN_ID) >> IXGBE_STATUS_LAN_ID_SHIFT) as u16;
	let lan_id = func as u8;

	/* check for a port swap */
	reg = ixgbe_hw::read_reg(info, IXGBE_FACTPS)?; 
	if reg & IXGBE_FACTPS_LFS != 0 {
		func ^= 0x1;
    }

	/* Get MAC instance from EEPROM for configuring CS4227 */
    let mut ee_ctrl_4 = [0;1];
    let mut instance_id = 0;
	if info.id == IXGBE_DEV_ID_X550EM_A_SFP {
		self.read_eerd(info,&mut hw.eeprom,IXGBE_EEPROM_CTRL_4, &mut ee_ctrl_4)?;
		instance_id = (ee_ctrl_4[0] & IXGBE_EE_CTRL_4_INST_ID) >>
				   IXGBE_EE_CTRL_4_INST_ID_SHIFT;
	}

    Ok((func, lan_id, instance_id))
}


    //fn disable_mc(&PCIeInfo, ) -> Result<(), IxgbeDriverErr>{
    //if ()
    //}

    // ixgbe_acquire_swhw_sync() For X540 ixgbe_acquire_swfw_sync_X540()
    // Acquires the SWFW semaphore through the GSSR register for the specified function (CSR, PHY0, PHY1, EEPROM, Flash)
    fn mac_acquire_swfw_sync(&self, info: &PCIeInfo, mask: u32) -> Result<(), IxgbeDriverErr> {
        let mut gssr = 0;
        let timeout = 200;
        let swmask = mask;
        let fwmask = mask << 5;

        for _ in 0..timeout {
            // SW NVM semaphore bit is used for access to all
            // SW_FW_SYNC bits (not just NVM)

            get_eeprom_semaphore(info)?;

            gssr = ixgbe_hw::read_reg(info, IXGBE_GSSR)?;
            if !(gssr & (fwmask | swmask)) != 0 {
                gssr |= swmask;
                ixgbe_hw::write_reg(info, IXGBE_GSSR, gssr)?;
                release_eeprom_semaphore(info)?;
                return Ok(());
            } else {
                release_eeprom_semaphore(info)?;
                awkernel_lib::delay::wait_microsec(5);
            }
        }

        // If time expired clear the bits holding the lock and retry
        if gssr & (fwmask | swmask) != 0 {
            self.mac_release_swfw_sync(info, gssr & (fwmask | swmask))?;
        }

        awkernel_lib::delay::wait_microsec(5);
        Err(SwfwSync)
    }

    // ixgbe_release_swhw_sync() For X540 ixgbe_release_swfw_sync_X540()
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

  // get_bus_info - Generic set PCI bus info
  // Gets the PCI bus info (speed, width, type) then calls helper function to
  // store this data within the ixgbe_hw structure.
    fn mac_get_bus_info(&self, info: &mut PCIeInfo, hw: &mut IxgbeHw) -> Result<IxgbeBusInfo, IxgbeDriverErr>{
        let Some(cap) = info.get_pcie_cap_mut() else {
            return Err(NotPciExpress);
        };
        let val = cap.get_link_status_control();
        let link_status = (val.bits() & 0xFFFF) as u16;

        set_pci_config_data(self, info, hw, link_status)
    }


    fn mac_enable_rx(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr>{
        use ixgbe_hw::MacType::*;
        let rxctrl = ixgbe_hw::read_reg(info, IXGBE_RXCTRL)?;
        ixgbe_hw::write_reg(info, IXGBE_RXCTRL, rxctrl | IXGBE_RXCTRL_RXEN)?;
        if hw.mac.mac_type != IxgbeMac82598EB {
            if hw.mac.set_lben {
                let mut pfdtxgswc = ixgbe_hw::read_reg(info, IXGBE_PFDTXGSWC)?;
                pfdtxgswc |= IXGBE_PFDTXGSWC_VT_LBEN as u32;
                ixgbe_hw::write_reg(info, IXGBE_PFDTXGSWC, pfdtxgswc)?;
                hw.mac.set_lben = false;
            }
        }
        Ok(())
    }
    fn mac_disable_rx(&self, info:&PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr>{
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
    fn mac_enable_rx_dma(&self, info: &PCIeInfo, hw: &mut IxgbeHw, regval: u32) -> Result<(), IxgbeDriverErr>{
        if regval & IXGBE_RXCTRL_RXEN != 0 {
            self.mac_enable_rx(info, hw)?;
        } else {
            self.mac_disable_rx(info, hw)?;
        }
        Ok(())
    }

    fn mac_get_link_capabilities(&self) -> Result<(), IxgbeDriverErr>;



    // PHY Operations

    // ixgbe_read_phy_reg_generic()
    fn phy_read_reg(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        reg_addr: u32,
        device_type: u32,
    ) -> Result<u16, IxgbeDriverErr> {
        let status;
        let gssr = hw.phy.phy_semaphore_mask;

        self.mac_acquire_swfw_sync(info, gssr)?;

        status = self.phy_read_reg_mdi(info, hw, reg_addr, device_type)?;

        self.mac_release_swfw_sync(info, gssr)?;

        Ok(status)
    }

    fn phy_write_reg(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        reg_addr: u32,
        device_type: u32,
        phy_data: u16,
    ) -> Result<(), IxgbeDriverErr> {
        let status;
        let gssr = hw.phy.phy_semaphore_mask;

        self.mac_acquire_swfw_sync(info, gssr)?;

        status = self.write_reg_mdi(info, hw, reg_addr, device_type, phy_data);

        status
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

    fn write_reg_mdi(
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

    //fn set_phy_power(&self, info: &PCIeInfo, hw: &IxgbeHw, on: bool) -> Result<(), IxgbeDriverErr>;
    fn phy_set_power(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        on: bool,
    ) -> Result<(), IxgbeDriverErr>;

    // EEPROM Operations

    fn init_params(&self, info: &PCIeInfo) -> Result<(EepromType, u32, u16), IxgbeDriverErr> {
        Err(NotSupported)
    }

    fn read_eerd(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
        offset: u16,
        data: &mut [u16],
    ) -> Result<(), IxgbeDriverErr> {
        let ret = read_eerd_buffer_generic(self, info, eeprom, offset, 1, data)?;
        Ok(ret)
    }

    fn validate_eeprom_checksum(&self, info: &PCIeInfo) -> Result<IxgbeEepromInfo, IxgbeDriverErr>;

    fn calc_eeprom_checksum(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
    ) -> Result<u16, IxgbeDriverErr>;
}
