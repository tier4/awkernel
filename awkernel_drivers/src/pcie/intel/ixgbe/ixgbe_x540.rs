use super::{
    ixgbe_hw::{self, IxgbeMediaType},
    ixgbe_operations::{self, IxgbeOperations},
    ixgbe_regs::*,
    Ixgbe, IxgbeDriverErr,
};
use crate::pcie::PCIeInfo;
use alloc::boxed::Box;
use awkernel_lib::{delay::wait_microsec, sanity::check};
use ixgbe_hw::{
    EepromType, IxgbeEepromInfo, IxgbeHw, IxgbeMacInfo, IxgbePhyInfo, MacType, MediaType,
};

const IXGBE_X540_MAX_TX_QUEUES: u32 = 128;
const IXGBE_X540_MAX_RX_QUEUES: u32 = 128;
const IXGBE_X540_RAR_ENTRIES: u32 = 128;
const IXGBE_X540_MC_TBL_SIZE: u32 = 128;
const IXGBE_X540_VFT_TBL_SIZE: u32 = 128;
const IXGBE_X540_RX_PB_SIZE: u32 = 384;

pub struct IxgbeX540;

fn mng_present(info: &PCIeInfo, mac_type: &MacType) -> Result<bool, IxgbeDriverErr> {
    use MacType::*;
    let fwsm;

    if matches!(mac_type, IxgbeMac82599EB) {
        return Ok(false);
    }

    fwsm = ixgbe_hw::read_reg(info, IXGBE_FWSM)?;

    Ok((fwsm & IXGBE_FWSM_FW_MODE_PT as u32) != 0)
}

// This function checks the MMNGC.MNG_VITO bit to see it there are any constraints on link from manageablity.
fn check_reset_blocked(info: &PCIeInfo, mac_type: &MacType) -> Result<bool, IxgbeDriverErr> {
    use MacType::*;
    let mmngc;

    // If we don't have this bit, it can't be blocking
    if matches!(mac_type, IxgbeMac82598EB) {
        return Ok(false);
    }

    mmngc = ixgbe_hw::read_reg(info, IXGBE_MMNGC)?;
    if mmngc & IXGBE_MMNGC_MNG_VETO != 0 {
        log::error!("MNG_VETO bit detected");
        return Ok(true);
    }

    Ok(false)
}
impl IxgbeX540 {
    fn new() -> Self {
        Self
    }
}

pub fn get_self() -> Box<dyn IxgbeOperations> {
    let ops = IxgbeX540::new();

    Box::new(ops)
}

impl IxgbeOperations for IxgbeX540 {
    // MAC Operations

    // ixgbe_reset_hw_X540 - Perform hardware reset
    // Resets the hardware by resetting the transmit and receive units, masks
    // and clears all interrupts, and perform a reset.
    fn mac_reset_hw(&self, info: &mut PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        self.mac_stop_adapter(info, hw)?;

        ixgbe_operations::clear_tx_pending(info, hw)?;

        let mut ctrl;
        let mut status = Ok(());
        'double_reset: loop {
            status = Ok(());
            self.mac_acquire_swfw_sync(info, hw.phy.phy_semaphore_mask)?;
            ctrl = IXGBE_CTRL_RST;
            ctrl |= ixgbe_hw::read_reg(info, IXGBE_CTRL)?;
            ixgbe_hw::write_reg(info, IXGBE_CTRL, ctrl)?;
            ixgbe_hw::write_flush(info)?;
            self.mac_release_swfw_sync(info, hw.phy.phy_semaphore_mask)?;

            /* Poll for reset bit to self-clear indicating reset is complete */
            for _ in 0..10 {
                wait_microsec(1);
                ctrl = ixgbe_hw::read_reg(info, IXGBE_CTRL)?;
                if ctrl & IXGBE_CTRL_RST_MASK == 0 {
                    break;
                }
            }

            if ctrl & IXGBE_CTRL_RST_MASK != 0 {
                // Do not return immediately here as it might double reset.
                status = Err(IxgbeDriverErr::ResetFailed);
                log::error!("Reset polling failed to complete.");
            }
            wait_microsec(100);

            // Double resets are required for recovery from certain error
            // conditions. Between resets, it is necessary to stall to allow time
            // for any pending HW events to complete.
            if hw.mac.flags & IXGBE_FLAGS_DOUBLE_RESET_REQUIRED == 0 {
                hw.mac.flags &= !(IXGBE_FLAGS_DOUBLE_RESET_REQUIRED);
                break 'double_reset;
            }
        }

        // Set the Rx packet buffer size.
        ixgbe_hw::write_reg(info, IXGBE_RXPBSIZE(0), 384 << IXGBE_RXPBSIZE_SHIFT)?;

        // Store the permanent mac address
        self.mac_get_mac_addr(info, &mut hw.mac.perm_addr)?;
        log::debug!("After get_mac_addr() IxgbeMacInfo:{:?}", hw.mac);

        // Store MAC address from RAR0, clear receive address registers, and
        // clear the multicast table.  Also reset num_rar_entries to 128,
        // since we modify this value when programming the SAN MAC address.
        hw.mac.num_rar_entries = IXGBE_X540_RAR_ENTRIES;
        self.mac_init_rx_addrs(info, hw)?;

        status
    }

    fn mac_start_hw(&self, info: &PCIeInfo, hw: &IxgbeHw) -> Result<(), IxgbeDriverErr> {
        start_hw_generic(self, info, hw)?;
        start_hw_generic2(info, hw)?;
    }

    fn mac_get_media_type(&self) -> Result<MediaType, IxgbeDriverErr> {
        Ok(MediaType::IxgbeMediaTypeCopper)
    }

    // PHY Operations
    // Using copper phy
    fn set_phy_power(
        &self,
        info: &PCIeInfo,
        //hw: &IxgbeHw,
        mac_type: &MacType,
        phy_addr: u32,
        phy_semaphore_mask: u32,
        on: bool,
    ) -> Result<(), IxgbeDriverErr> {
        let status;
        let mut reg;

        // What is this for?
        if !on && mng_present(info, mac_type)? {
            return Ok(()); // Don't know if this is correct.
        }

        reg = self.phy_read_reg(
            info,
            phy_addr,
            phy_semaphore_mask,
            IXGBE_MDIO_VENDOR_SPECIFIC_1_CONTROL,
            IXGBE_MDIO_VENDOR_SPECIFIC_1_DEV_TYPE,
        )?;

        if on {
            reg &= !(IXGBE_MDIO_PHY_SET_LOW_POWER_MODE as u16);
        } else {
            if check_reset_blocked(info, mac_type)? {
                return Ok(()); // Not sure if this is correct.
            }
            reg |= IXGBE_MDIO_PHY_SET_LOW_POWER_MODE as u16;
        }

        status = self.phy_write_reg(
            info,
            phy_addr,
            phy_semaphore_mask,
            IXGBE_MDIO_VENDOR_SPECIFIC_1_CONTROL,
            IXGBE_MDIO_VENDOR_SPECIFIC_1_DEV_TYPE,
            reg,
        );

        status
    }

    // EEPROM Operations

    /* Requires checking of EepromType to make sure that it is uninitialized beforehand*/
    fn init_params(&self, info: &PCIeInfo) -> Result<(EepromType, u32, u16), IxgbeDriverErr> {
        let eec = ixgbe_hw::read_reg(info, IXGBE_EEC_X540)?;
        let eeprom_size = (eec & IXGBE_EEC_SIZE) >> IXGBE_EEC_SIZE_SHIFT as u16;
        let word_size = 1 << (eeprom_size + IXGBE_EEPROM_WORD_SIZE_SHIFT);

        Ok((EepromType::IxgbeFlash, 10, word_size))
    }

    fn read_eerd(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
        offset: u16,
        data: &mut [u16],
    ) -> Result<(), IxgbeDriverErr> {
        self.mac_acquire_swfw_sync(info, IXGBE_GSSR_EEP_SM)?;
        let ret = ixgbe_operations::read_eerd_buffer_generic(self, info, eeprom, offset, 1, data);
        self.mac_release_swfw_sync(info, IXGBE_GSSR_EEP_SM)?;
        ret
    }

    fn validate_eeprom_checksum(&self, info: &PCIeInfo) -> Result<IxgbeEepromInfo, IxgbeDriverErr> {
        let mut eeprom = IxgbeEepromInfo {
            eeprom_type: EepromType::IxgbeEepromUninitialized,
            semaphore_delay: 0,
            word_size: 0,
            address_bits: 0,
            word_page_size: 0,
            ctrl_word_3: 0,
        };
        let mut data = [0; 1];
        let checksum;

        self.read_eerd(info, &mut eeprom, 0, &mut data)?;
        log::info!("eeprom.word_size:{}", eeprom.word_size);

        self.mac_acquire_swfw_sync(info, IXGBE_GSSR_EEP_SM)?;

        match self.calc_eeprom_checksum(info, &mut eeprom) {
            Ok(ret) => {
                checksum = ret;
            }
            Err(e) => {
                self.mac_release_swfw_sync(info, IXGBE_GSSR_EEP_SM)?;
                return Err(e);
            }
        }

        // Do not use self.read_eerd() because we do not want to
        // take the synchronization semaphore twice here. */
        let mut read_checksum = [0; 1];
        if let Err(e) = ixgbe_operations::read_eerd_buffer_generic(
            self,
            info,
            &mut eeprom,
            IXGBE_EEPROM_CHECKSUM as u16,
            1,
            &mut read_checksum,
        ) {
            self.mac_release_swfw_sync(info, IXGBE_GSSR_EEP_SM)?;
            return Err(e);
        }

        // Verify read checksum from EEPROM is the same as
        // calculated checksum
        if read_checksum[0] != checksum {
            log::error!("Invalid EEPROM checksum");
            return Err(IxgbeDriverErr::EepromChecksum);
        }

        Ok(eeprom)
    }

    fn calc_eeprom_checksum(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
    ) -> Result<u16, IxgbeDriverErr> {
        // Do not use self.read_eerd() because we do not want to
        // take the synchronization semaphore twice here.

        let mut checksum = 0;
        let ptr_start = IXGBE_PCIE_ANALOG_PTR;
        //Include 0x0 up to IXGBE_EEPROM_CHECKSUM; do not include the
        // checksum itself
        let mut word = [0; 1];
        for i in 0..IXGBE_EEPROM_CHECKSUM {
            ixgbe_operations::read_eerd_buffer_generic(self, info, eeprom, i, 1, &mut word)?;
            checksum += word[0];
        }

        //  Include all data from pointers 0x3, 0x6-0xE.  This excludes the
        // FW, PHY module, and PCIe Expansion/Option ROM pointers.
        let mut pointer = [0; 1];
        let mut length = [0; 1];
        for i in ptr_start..IXGBE_FW_PTR {
            if i == IXGBE_PHY_PTR || i == IXGBE_OPTION_ROM_PTR {
                continue;
            }

            ixgbe_operations::read_eerd_buffer_generic(self, info, eeprom, i, 1, &mut pointer)?;

            // Skip pointer section if the pointer is invalid.
            if pointer[0] == 0xFFFF || pointer[0] == 0 || pointer[0] >= eeprom.word_size {
                continue;
            }

            ixgbe_operations::read_eerd_buffer_generic(
                self,
                info,
                eeprom,
                pointer[0],
                1,
                &mut length,
            )?;

            // Skip pointer section if the pointer is invalid.
            if length[0] == 0xFFFF || length[0] == 0 || (pointer[0] + length[0]) >= eeprom.word_size
            {
                continue;
            }

            for j in pointer[0] + 1..=pointer[0] + length[0] {
                ixgbe_operations::read_eerd_buffer_generic(self, info, eeprom, j, 1, &mut word)?;
                checksum += word[0];
            }
        }

        checksum = IXGBE_EEPROM_SUM - checksum;

        Ok(checksum)
    }
}

pub fn set_mac_val(
    info: &PCIeInfo,
) -> Result<(u32, u32, u32, u32, u32, u32, u16, bool), IxgbeDriverErr> {
    let arc_subsystem_valid = match ixgbe_hw::read_reg(info, IXGBE_FWSM_X540 & IXGBE_FWSM_MODE_MASK)
    {
        Ok(val) => {
            if val == 0 {
                false
            } else {
                true
            }
        }
        Err(e) => return Err(e),
    };

    Ok((
        IXGBE_X540_MC_TBL_SIZE,
        IXGBE_X540_VFT_TBL_SIZE,
        IXGBE_X540_RAR_ENTRIES,
        IXGBE_X540_RX_PB_SIZE,
        IXGBE_X540_MAX_RX_QUEUES,
        IXGBE_X540_MAX_TX_QUEUES,
        0,
        arc_subsystem_valid,
    ))
}
