use core::fmt::Arguments;

use super::{
    ixgbe_hw::{self, EepromType, IxgbeEepromInfo, IxgbeMediaType},
    ixgbe_regs::*,
    Ixgbe,
    IxgbeDriverErr::{self, *},
};
use crate::pcie::{capability::pcie_cap::PCIeCap, PCIeInfo};
use awkernel_lib::delay::wait_microsec;
use ixgbe_hw::{IxgbeHw, MacType};

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
pub fn start_hw_generic<T: IxgbeOperations + ?Sized>(ops: &T,info: &PCIeInfo, hw: &IxgbeHw){
	/* Set the media type */
	hw.phy.media_type = ops.mac_get_media_type();

	/* PHY ops initialization must be done in reset_hw() */

	/* Clear the VLAN filter table */
	ops.mac_clear_vfta(hw);

	/* Clear statistics registers */
	hw->mac.ops.clear_hw_cntrs(hw);

	/* Set No Snoop Disable */
	ctrl_ext = IXGBE_READ_REG(hw, IXGBE_CTRL_EXT);
	ctrl_ext |= IXGBE_CTRL_EXT_NS_DIS;
	IXGBE_WRITE_REG(hw, IXGBE_CTRL_EXT, ctrl_ext);
	IXGBE_WRITE_FLUSH(hw);

	/* Setup flow control */
	if (hw->mac.ops.setup_fc) {
		ret_val = hw->mac.ops.setup_fc(hw);
		if (ret_val != IXGBE_SUCCESS) {
			DEBUGOUT1("Flow control setup failed, returning %d\n", ret_val);
			return ret_val;
		}
	}

	/* Cache bit indicating need for crosstalk fix */
	switch (hw->mac.type) {
	case ixgbe_mac_82599EB:
	case ixgbe_mac_X550EM_x:
	case ixgbe_mac_X550EM_a:
		hw->mac.ops.get_device_caps(hw, &device_caps);
		if (device_caps & IXGBE_DEVICE_CAPS_NO_CROSSTALK_WR)
			hw->need_crosstalk_fix = FALSE;
		else
			hw->need_crosstalk_fix = TRUE;
		break;
	default:
		hw->need_crosstalk_fix = FALSE;
		break;
	}

	/* Clear adapter stopped flag */
	hw->adapter_stopped = FALSE;

	return IXGBE_SUCCESS;
}



// ixgbe_validate_mac_addr - Validate MAC address
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

// ixgbe_validate_mac_addr - Validate MAC address
// Tests a MAC address to ensure it is a valid Individual Address

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
            Ok(()) | Err(SfpNotPresent) => self.start_hw(info, hw)?,
            Err(e) => Err(e),
        };

        ret
    }

    fn mac_reset_hw(&self, info: &mut PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        Ok(())
    }

    fn mac_start_hw(&self, info: &PCIeInfo, hw: &IxgbeHw) -> Result<(), IxgbeDriverErr>;

    fn mac_get_media_type(&self)->Result<IxgbeMediaType, IxgbeDriverErr>;

    // clear_vfta- Clear VLAN filter table
    // Clears the VLAN filer table, and the VMDq index associated with the filter
    fn mac_clear_vfta(&self, info: &PCIeInfo, hw: &IxgbeHw) -> Result<(), IxgbeDriverErr> {
        for offset in 0..hw.mac.vft_size {
            ixgbe_hw::write_reg(info, IXGBE_VFTA(offset) as usize, 0)?;
        }

        for offset in 0..IXGBE_VLVF_ENTRIES {
            ixgbe_hw::write_reg(info, IXGBE_VLVF(offset) as usize, 0)?;
            ixgbe_hw::write_reg(info, IXGBE_VLVFB(offset * 2) as usize, 0)?;
            ixgbe_hw::write_reg(info, IXGBE_VLVFB((offset * 2) + 1) as usize, 0)?;
        }

        Ok(())
    }

 // clear_hw_cntrs - Generic clear hardware counters
 // Clears all hardware statistics counters by reading them from the hardware
 // Statistics counters are clear on read.
fn clear_hw_cntrs(&self, info: &PCIeInfo, hw: &IxgbeHw)->Result<(),IxgbeDriverErr>{
    use ixgbe_hw::{read_reg,write_reg};
	read_reg(info, IXGBE_CRCERRS)?;
	read_reg(info, IXGBE_ILLERRC)?;
	read_reg(info, IXGBE_ERRBC)?;
	read_reg(info, IXGBE_MSPDC)?;
	for _ in 0..8 {
		read_reg(info, IXGBE_MPC(i));
    
    }

	read_reg(info, IXGBE_MLFC)?;
	read_reg(info, IXGBE_MRFC)?;
	read_reg(info, IXGBE_RLEC)?;
	read_reg(info, IXGBE_LXONTXC)?;
	read_reg(info, IXGBE_LXOFFTXC)?;

	if (hw->mac.type >= ixgbe_mac_82599EB) {
		IXGBE_READ_REG(hw, IXGBE_LXONRXCNT);
		IXGBE_READ_REG(hw, IXGBE_LXOFFRXCNT);
	} else {
		IXGBE_READ_REG(hw, IXGBE_LXONRXC);
		IXGBE_READ_REG(hw, IXGBE_LXOFFRXC);
	}

	for (i = 0; i < 8; i++) {
		IXGBE_READ_REG(hw, IXGBE_PXONTXC(i));
		IXGBE_READ_REG(hw, IXGBE_PXOFFTXC(i));
		if (hw->mac.type >= ixgbe_mac_82599EB) {
			IXGBE_READ_REG(hw, IXGBE_PXONRXCNT(i));
			IXGBE_READ_REG(hw, IXGBE_PXOFFRXCNT(i));
		} else {
			IXGBE_READ_REG(hw, IXGBE_PXONRXC(i));
			IXGBE_READ_REG(hw, IXGBE_PXOFFRXC(i));
		}
	}
	if (hw->mac.type >= ixgbe_mac_82599EB)
		for (i = 0; i < 8; i++)
			IXGBE_READ_REG(hw, IXGBE_PXON2OFFCNT(i));
	IXGBE_READ_REG(hw, IXGBE_PRC64);
	IXGBE_READ_REG(hw, IXGBE_PRC127);
	IXGBE_READ_REG(hw, IXGBE_PRC255);
	IXGBE_READ_REG(hw, IXGBE_PRC511);
	IXGBE_READ_REG(hw, IXGBE_PRC1023);
	IXGBE_READ_REG(hw, IXGBE_PRC1522);
	IXGBE_READ_REG(hw, IXGBE_GPRC);
	IXGBE_READ_REG(hw, IXGBE_BPRC);
	IXGBE_READ_REG(hw, IXGBE_MPRC);
	IXGBE_READ_REG(hw, IXGBE_GPTC);
	IXGBE_READ_REG(hw, IXGBE_GORCL);
	IXGBE_READ_REG(hw, IXGBE_GORCH);
	IXGBE_READ_REG(hw, IXGBE_GOTCL);
	IXGBE_READ_REG(hw, IXGBE_GOTCH);
	if (hw->mac.type == ixgbe_mac_82598EB)
		for (i = 0; i < 8; i++)
			IXGBE_READ_REG(hw, IXGBE_RNBC(i));
	IXGBE_READ_REG(hw, IXGBE_RUC);
	IXGBE_READ_REG(hw, IXGBE_RFC);
	IXGBE_READ_REG(hw, IXGBE_ROC);
	IXGBE_READ_REG(hw, IXGBE_RJC);
	IXGBE_READ_REG(hw, IXGBE_MNGPRC);
	IXGBE_READ_REG(hw, IXGBE_MNGPDC);
	IXGBE_READ_REG(hw, IXGBE_MNGPTC);
	IXGBE_READ_REG(hw, IXGBE_TORL);
	IXGBE_READ_REG(hw, IXGBE_TORH);
	IXGBE_READ_REG(hw, IXGBE_TPR);
	IXGBE_READ_REG(hw, IXGBE_TPT);
	IXGBE_READ_REG(hw, IXGBE_PTC64);
	IXGBE_READ_REG(hw, IXGBE_PTC127);
	IXGBE_READ_REG(hw, IXGBE_PTC255);
	IXGBE_READ_REG(hw, IXGBE_PTC511);
	IXGBE_READ_REG(hw, IXGBE_PTC1023);
	IXGBE_READ_REG(hw, IXGBE_PTC1522);
	IXGBE_READ_REG(hw, IXGBE_MPTC);
	IXGBE_READ_REG(hw, IXGBE_BPTC);
	for (i = 0; i < 16; i++) {
		IXGBE_READ_REG(hw, IXGBE_QPRC(i));
		IXGBE_READ_REG(hw, IXGBE_QPTC(i));
		if (hw->mac.type >= ixgbe_mac_82599EB) {
			IXGBE_READ_REG(hw, IXGBE_QBRC_L(i));
			IXGBE_READ_REG(hw, IXGBE_QBRC_H(i));
			IXGBE_READ_REG(hw, IXGBE_QBTC_L(i));
			IXGBE_READ_REG(hw, IXGBE_QBTC_H(i));
			IXGBE_READ_REG(hw, IXGBE_QPRDC(i));
		} else {
			IXGBE_READ_REG(hw, IXGBE_QBRC(i));
			IXGBE_READ_REG(hw, IXGBE_QBTC(i));
		}
	}

	if (hw->mac.type == ixgbe_mac_X550 || hw->mac.type == ixgbe_mac_X540) {
		if (hw->phy.id == 0)
			ixgbe_identify_phy(hw);
		hw->phy.ops.read_reg(hw, IXGBE_PCRC8ECL,
				     IXGBE_MDIO_PCS_DEV_TYPE, &i);
		hw->phy.ops.read_reg(hw, IXGBE_PCRC8ECH,
				     IXGBE_MDIO_PCS_DEV_TYPE, &i);
		hw->phy.ops.read_reg(hw, IXGBE_LDPCECL,
				     IXGBE_MDIO_PCS_DEV_TYPE, &i);
		hw->phy.ops.read_reg(hw, IXGBE_LDPCECH,
				     IXGBE_MDIO_PCS_DEV_TYPE, &i);
	}

	return IXGBE_SUCCESS;
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
        self.mac_clear_vmdq(info, hw.mac.num_rar_entries, 0, IXGBE_CLEAR_VMDQ_ALL);

        hw.addr_ctrl.overflow_promisc = 0;

        hw.addr_ctrl.rar_used_count = 1;

        /* Zero out the other receive addresses. */
        for i in 0..hw.mac.num_rar_entries {
            ixgbe_hw::write_reg(info, IXGBE_RAL(i) as usize, 0);
            ixgbe_hw::write_reg(info, IXGBE_RAH(i) as usize, 0);
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
        self.mac_clear_vmdq(info, num_rar_entries, index, IXGBE_CLEAR_VMDQ_ALL);

        Ok(())
    }

    // mac_set_rar_generic - Set Rx address register
    // Puts an ethernet address into a receive address register.
    fn mac_set_rar(
        &self,
        info: &PCIeInfo,
        num_rar_entries: u32,
        index: u32,
        addr: &mut [u8],
        vmdq: u32,
        enable_addr: u32,
    ) -> Result<(), IxgbeDriverErr> {
        // Make sure we are using a valid rar index range
        if index >= num_rar_entries {
            log::error!("RAR index {} is out of range.\n", index);
            return Err(IxgbeDriverErr::InvalidArgument);
        }

        // setup VMDq pool selection before this RAR gets enabled
        self.mac_set_vmdq(info, num_rar_entries, index, vmdq);

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
            ixgbe_hw::write_reg(info, IXGBE_MPSAR_LO(rar) as usize, mpsar);
        } else {
            mpsar = ixgbe_hw::read_reg(info, IXGBE_MPSAR_HI(rar) as usize)?;
            mpsar |= 1 << (vmdq - 32);
            ixgbe_hw::write_reg(info, IXGBE_MPSAR_HI(rar) as usize, mpsar);
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
            self.mac_clear_rar(info, num_rar_entries, rar);
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

    fn mac_disable_rx(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        let mut rxctrl = ixgbe_hw::read_reg(info, IXGBE_RXCTRL)?;

        if rxctrl & IXGBE_RXCTRL_RXEN != 0 {
            let mut pfdtxgswc = ixgbe_hw::read_reg(info, IXGBE_PFDTXGSWC)?;
            if pfdtxgswc & IXGBE_PFDTXGSWC_VT_LBEN as u32 != 0 {
                pfdtxgswc &= !(IXGBE_PFDTXGSWC_VT_LBEN as u32);
                ixgbe_hw::write_reg(info, IXGBE_PFDTXGSWC, pfdtxgswc)?;
                hw.mac.set_lben = true;
            } else {
                hw.mac.set_lben = false;
            }

            rxctrl &= !IXGBE_RXCTRL_RXEN;
            ixgbe_hw::write_reg(info, IXGBE_RXCTRL, rxctrl)?;
        }

        Ok(())
    }

    //fn disable_mc(&PCIeInfo, ) -> Result<(), IxgbeDriverErr>{
    //if ()
    //}

    // ixgbe_get_bus_info_generic()
    //fn mac_get_bus_info(&self, hw: &IxgbeHw) -> Result<(), IxgbeDriverErr>;

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

    // PHY Operations

    // ixgbe_read_phy_reg_generic()
    fn phy_read_reg(
        &self,
        info: &PCIeInfo,
        //hw: &IxgbeHw,
        phy_addr: u32,
        phy_semaphore_mask: u32,
        reg_addr: u32,
        device_type: u32,
    ) -> Result<u16, IxgbeDriverErr> {
        let status;
        let gssr = phy_semaphore_mask;

        self.mac_acquire_swfw_sync(info, gssr)?;

        status = self.phy_read_reg_mdi(info, phy_addr, reg_addr, device_type)?;

        self.mac_release_swfw_sync(info, gssr)?;

        Ok(status)
    }

    fn phy_write_reg(
        &self,
        info: &PCIeInfo,
        //hw: &IxgbeHw,
        phy_addr: u32,
        phy_semaphore_mask: u32,
        reg_addr: u32,
        device_type: u32,
        phy_data: u16,
    ) -> Result<(), IxgbeDriverErr> {
        let status;
        //let gssr = hw.phy.phy_semaphore_mask;
        let gssr = phy_semaphore_mask;

        self.mac_acquire_swfw_sync(info, gssr)?;

        status = self.write_reg_mdi(info, phy_addr, reg_addr, device_type, phy_data);

        status
    }

    fn phy_read_reg_mdi(
        &self,
        info: &PCIeInfo,
        //hw: &IxgbeHw,
        phy_addr: u32,
        reg_addr: u32,
        device_type: u32,
    ) -> Result<u16, IxgbeDriverErr> {
        let mut command: u32 = (reg_addr << IXGBE_MSCA_NP_ADDR_SHIFT)
            | (device_type << IXGBE_MSCA_DEV_TYPE_SHIFT)
            | (phy_addr << IXGBE_MSCA_PHY_ADDR_SHIFT)
            | (IXGBE_MSCA_ADDR_CYCLE | IXGBE_MSCA_MDI_COMMAND) as u32;

        ixgbe_hw::write_reg(info, IXGBE_MSCA, command)?;

        command = check_address_cycle_complete(info)?;
        if (command & IXGBE_MSCA_MDI_COMMAND as u32) != 0 {
            log::error!("PHY address command did not complete");
            return Err(Phy);
        }

        command = (reg_addr << IXGBE_MSCA_NP_ADDR_SHIFT)
            | (device_type << IXGBE_MSCA_DEV_TYPE_SHIFT)
            | (phy_addr << IXGBE_MSCA_PHY_ADDR_SHIFT)
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
        phy_addr: u32,
        //hw: &IxgbeHw,
        reg_addr: u32,
        device_type: u32,
        phy_data: u16,
    ) -> Result<(), IxgbeDriverErr> {
        // Put the data in the MDI single read write data register
        ixgbe_hw::write_reg(info, IXGBE_MSRWD, phy_data as u32)?;

        let mut command = (reg_addr << IXGBE_MSCA_NP_ADDR_SHIFT)
            | (device_type << IXGBE_MSCA_DEV_TYPE_SHIFT)
            | (phy_addr << IXGBE_MSCA_PHY_ADDR_SHIFT)
            | (IXGBE_MSCA_ADDR_CYCLE | IXGBE_MSCA_MDI_COMMAND) as u32;

        ixgbe_hw::write_reg(info, IXGBE_MSCA, command)?;

        command = check_address_cycle_complete(info)?;
        if (command & IXGBE_MSCA_MDI_COMMAND as u32) != 0 {
            log::error!("PHY address command did not complete");
            return Err(Phy);
        }

        command = (reg_addr << IXGBE_MSCA_NP_ADDR_SHIFT)
            | (device_type << IXGBE_MSCA_DEV_TYPE_SHIFT)
            | (phy_addr << IXGBE_MSCA_PHY_ADDR_SHIFT)
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
    fn set_phy_power(
        &self,
        info: &PCIeInfo,
        mac_type: &MacType,
        phy_addr: u32,
        phy_semaphore_mask: u32,
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
