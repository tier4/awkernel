use super::{
    ixgbe_hw,
    ixgbe_operations::{self, start_hw_gen2, start_hw_generic, IxgbeOperations},
    ixgbe_regs::*,
    IxgbeDriverErr,
};
use crate::pcie::PCIeInfo;
use alloc::boxed::Box;
use awkernel_lib::delay::{wait_microsec, wait_millisec};
use ixgbe_hw::{EepromType, IxgbeEepromInfo, IxgbeHw, MacType, MediaType};
use ixgbe_operations::get_copper_link_capabilities;

const IXGBE_X540_MAX_TX_QUEUES: u32 = 128;
const IXGBE_X540_MAX_RX_QUEUES: u32 = 128;
const IXGBE_X540_RAR_ENTRIES: u32 = 128;
const IXGBE_X540_MC_TBL_SIZE: u32 = 128;
const IXGBE_X540_VFT_TBL_SIZE: u32 = 128;
const IXGBE_X540_RX_PB_SIZE: u32 = 384;

pub struct IxgbeX540;

fn mng_present(info: &PCIeInfo, mac_type: &MacType) -> Result<bool, IxgbeDriverErr> {
    use MacType::*;

    if matches!(mac_type, IxgbeMac82599EB) {
        return Ok(false);
    }

    let fwsm = ixgbe_hw::read_reg(info, IXGBE_FWSM)?;

    Ok((fwsm & IXGBE_FWSM_FW_MODE_PT) != 0)
}

/// This function checks the MMNGC.MNG_VITO bit to see it there are any constraints on link from manageablity.
fn check_reset_blocked(info: &PCIeInfo, mac_type: &MacType) -> Result<bool, IxgbeDriverErr> {
    use MacType::*;

    // If we don't have this bit, it can't be blocking
    if matches!(mac_type, IxgbeMac82598EB) {
        return Ok(false);
    }

    let mmngc = ixgbe_hw::read_reg(info, IXGBE_MMNGC)?;
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

pub fn mac_reset_hw_x540<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &mut PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    ops.mac_stop_adapter(info, hw)?;

    ixgbe_operations::clear_tx_pending(info, hw)?;

    let mut status;
    'double_reset: loop {
        status = Ok(());

        ixgbe_operations::mac_swfw_sync_mut(ops, info, hw.phy.phy_semaphore_mask, 0, || {
            let mut ctrl = IXGBE_CTRL_RST;
            ctrl |= ixgbe_hw::read_reg(info, IXGBE_CTRL)?;
            ixgbe_hw::write_reg(info, IXGBE_CTRL, ctrl)?;
            ixgbe_hw::write_flush(info)
        })?;

        // Poll for reset bit to self-clear indicating reset is complete
        let mut ctrl = 0;
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
    ops.mac_get_mac_addr(info, &mut hw.mac.perm_addr)?;

    // Store MAC address from RAR0, clear receive address registers, and
    // clear the multicast table.  Also reset num_rar_entries to 128,
    // since we modify this value when programming the SAN MAC address.
    hw.mac.num_rar_entries = IXGBE_X540_RAR_ENTRIES;
    ops.mac_init_rx_addrs(info, hw)?;

    status
}

pub fn mac_start_hw_x540<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    start_hw_generic(ops, info, hw)?;
    start_hw_gen2(info, hw)?;

    Ok(())
}

pub fn get_swfw_sync_semaphore(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let swsm_offset = get_swsm_offset(info.get_id())?;
    let mut status = Err(IxgbeDriverErr::Eeprom);
    let timeout = 2000;
    // Get SMBI software semaphore between device drivers first
    for _ in 0..timeout {
        // If the SMBI bit is 0 when we read it, then the bit will be
        // set and we have the semaphore
        let swsm = ixgbe_hw::read_reg(info, swsm_offset)?;
        if swsm & IXGBE_SWSM_SMBI == 0 {
            status = Ok(());
            break;
        }
        wait_microsec(50);
    }

    let swfw_sync_offset = get_swfw_sync_offset(info.get_id())?;
    // Now get the semaphore between SW/FW through the REGSMP bit
    if status.is_ok() {
        let mut i = 0;
        while i < timeout {
            match ixgbe_hw::read_reg(info, swfw_sync_offset) {
                Ok(swsm) => {
                    if swsm & IXGBE_SWFW_REGSMP == 0 {
                        break;
                    }
                }
                Err(e) => {
                    release_swfw_sync_semaphore(info)?;
                    return Err(e);
                }
            }

            wait_microsec(50);
            i += 1;
        }

        // Release semaphores and return error if SW NVM semaphore
        // was not granted because we don't have access to the EEPROM
        if i >= timeout {
            log::error!("REGSMP Software NVM semaphore not granted.");
            if let Err(e) = release_swfw_sync_semaphore(info) {
                log::error!("release_swfw_sync_semaphore failed.");
                return Err(e);
            }
            status = Err(IxgbeDriverErr::Eeprom);
        }
    } else {
        log::error!("Software semaphore SMBI between device drivers not granted.\n");
    }

    status
}

/// release_swfw_sync_semaphore - Release hardware semaphore
/// This function clears hardware semaphore bits.
fn release_swfw_sync_semaphore(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let swfw_sync_offset = get_swfw_sync_offset(info.get_id())?;
    let swsm_offset = get_swsm_offset(info.get_id())?;

    let mut swsm;
    // Release both semaphores by writing 0 to the bits REGSMP and SMBI
    swsm = ixgbe_hw::read_reg(info, swfw_sync_offset)?;
    swsm &= !IXGBE_SWFW_REGSMP;
    ixgbe_hw::write_reg(info, swfw_sync_offset, swsm)?;

    swsm = ixgbe_hw::read_reg(info, swsm_offset)?;
    swsm &= !IXGBE_SWSM_SMBI;
    ixgbe_hw::write_reg(info, swsm_offset, swsm)?;

    ixgbe_hw::write_flush(info)
}

pub fn mac_acquire_swfw_sync_x540(info: &PCIeInfo, mask: u32) -> Result<(), IxgbeDriverErr> {
    let swfw_sync_offset = get_swfw_sync_offset(info.get_id())?;

    let mut swmask = mask & IXGBE_GSSR_NVM_PHY_MASK;
    let mut fwmask = swmask << 5;
    let mut hwmask = 0;
    if swmask & IXGBE_GSSR_EEP_SM != 0 {
        hwmask |= IXGBE_GSSR_FLASH_SM;
    }

    /* SW only mask doesn't have FW bit pair */
    if mask & IXGBE_GSSR_SW_MNG_SM != 0 {
        swmask |= IXGBE_GSSR_SW_MNG_SM;
    }

    let swi2c_mask = mask & IXGBE_GSSR_I2C_MASK;
    swmask |= swi2c_mask;
    fwmask |= swi2c_mask << 2;

    let mut timeout = 200;
    if ixgbe_hw::get_mac_type(info.get_id())? >= MacType::IxgbeMacX550 {
        timeout = 1000;
    }

    let mut swfw_sync;
    for _ in 0..timeout {
        /* SW NVM semaphore bit is used for access to all
         * SW_FW_SYNC bits (not just NVM)
         */
        if get_swfw_sync_semaphore(info).is_err() {
            log::debug!(
                "Failed to get NVM access and register semaphore, returning IXGBE_ERR_SWFW_SYNC\n"
            );
            return Err(IxgbeDriverErr::SwfwSync);
        }

        match ixgbe_hw::read_reg(info, swfw_sync_offset) {
            Ok(ret) => swfw_sync = ret,
            Err(e) => {
                release_swfw_sync_semaphore(info)?;
                return Err(e);
            }
        }

        if swfw_sync & (fwmask | swmask | hwmask) == 0 {
            swfw_sync |= swmask;
            let status = ixgbe_hw::write_reg(info, swfw_sync_offset, swfw_sync);
            release_swfw_sync_semaphore(info)?;
            return status;
        }
        // Firmware currently using resource (fwmask), hardware
        // currently using resource (hwmask), or other software
        // thread currently using resource (swmask)
        release_swfw_sync_semaphore(info)?;
        wait_millisec(5);
    }

    // If the resource is not released by the FW/HW the SW can assume that
    // the FW/HW malfunctions. In that case the SW should set the SW bit(s)
    // of the requested resource(s) while ignoring the corresponding FW/HW
    // bits in the SW_FW_SYNC register.
    if get_swfw_sync_semaphore(info).is_err() {
        log::debug!("Failed to get NVM semaphore and register semaphore while forcefully ignoring FW semaphore bit(s) and setting SW semaphore bit(s), returning IXGBE_ERR_SWFW_SYNC\n");
        return Err(IxgbeDriverErr::SwfwSync);
    }
    match ixgbe_hw::read_reg(info, swfw_sync_offset) {
        Ok(ret) => swfw_sync = ret,
        Err(e) => {
            release_swfw_sync_semaphore(info)?;
            return Err(e);
        }
    }
    if swfw_sync & (fwmask | hwmask) != 0 {
        swfw_sync |= swmask;
        let status = ixgbe_hw::write_reg(info, swfw_sync_offset, swfw_sync);
        release_swfw_sync_semaphore(info)?;
        wait_millisec(5);
        return status;
    }
    // If the resource is not released by other SW the SW can assume that
    // the other SW malfunctions. In that case the SW should clear all SW
    // flags that it does not own and then repeat the whole process once
    // again.
    if swfw_sync & swmask != 0 {
        let mut rmask = IXGBE_GSSR_EEP_SM
            | IXGBE_GSSR_PHY0_SM
            | IXGBE_GSSR_PHY1_SM
            | IXGBE_GSSR_MAC_CSR_SM
            | IXGBE_GSSR_SW_MNG_SM;

        if swi2c_mask != 0 {
            rmask |= IXGBE_GSSR_I2C_MASK;
        }
        mac_release_swfw_sync_x540(info, rmask)?;
        release_swfw_sync_semaphore(info)?;
        log::debug!("Resource not released by other SW, returning IXGBE_ERR_SWFW_SYNC\n");
        return Err(IxgbeDriverErr::SwfwSync);
    }
    release_swfw_sync_semaphore(info)?;
    log::debug!("Returning error IXGBE_ERR_SWFW_SYNC\n");

    Err(IxgbeDriverErr::SwfwSync)
}

/// ixgbe_release_swfw_sync_X540 - Release SWFW semaphore
/// Releases the SWFW semaphore through the SW_FW_SYNC register
/// for the specified function (CSR, PHY0, PHY1, EVM, Flash)
pub fn mac_release_swfw_sync_x540(info: &PCIeInfo, mask: u32) -> Result<(), IxgbeDriverErr> {
    let mut swmask = mask & (IXGBE_GSSR_NVM_PHY_MASK | IXGBE_GSSR_SW_MNG_SM);
    if mask & IXGBE_GSSR_I2C_MASK != 0 {
        swmask |= mask & IXGBE_GSSR_I2C_MASK;
    }
    get_swfw_sync_semaphore(info)?;

    let swfw_sync_offset = get_swfw_sync_offset(info.get_id())?;
    let mut swfw_sync;
    swfw_sync = ixgbe_hw::read_reg(info, swfw_sync_offset)?;
    swfw_sync &= !swmask;
    ixgbe_hw::write_reg(info, swfw_sync_offset, swfw_sync)?;

    release_swfw_sync_semaphore(info)?;
    wait_microsec(2);

    Ok(())
}

pub fn phy_set_power_x540<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &IxgbeHw,
    on: bool,
) -> Result<(), IxgbeDriverErr> {
    let mut reg;

    // What is this for?
    if !on && mng_present(info, &hw.mac.mac_type)? {
        return Ok(()); // Don't know if this is correct.
    }

    reg = ops.phy_read_reg(
        info,
        hw,
        IXGBE_MDIO_VENDOR_SPECIFIC_1_CONTROL,
        IXGBE_MDIO_VENDOR_SPECIFIC_1_DEV_TYPE,
    )?;

    if on {
        reg &= !(IXGBE_MDIO_PHY_SET_LOW_POWER_MODE as u16);
    } else {
        if check_reset_blocked(info, &hw.mac.mac_type)? {
            return Ok(()); // Not sure if this is correct.
        }
        reg |= IXGBE_MDIO_PHY_SET_LOW_POWER_MODE as u16;
    }

    ops.phy_write_reg(
        info,
        hw,
        IXGBE_MDIO_VENDOR_SPECIFIC_1_CONTROL,
        IXGBE_MDIO_VENDOR_SPECIFIC_1_DEV_TYPE,
        reg,
    )?;

    Ok(())
}

impl IxgbeOperations for IxgbeX540 {
    // MAC Operations

    /// ixgbe_reset_hw_X540 - Perform hardware reset
    /// Resets the hardware by resetting the transmit and receive units, masks
    /// and clears all interrupts, and perform a reset.
    fn mac_reset_hw(&self, info: &mut PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        mac_reset_hw_x540(self, info, hw)
    }

    fn mac_start_hw(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        mac_start_hw_x540(self, info, hw)
    }

    fn mac_get_media_type(&self, _info: &PCIeInfo, _hw: &mut IxgbeHw) -> MediaType {
        MediaType::IxgbeMediaTypeCopper
    }

    fn mac_acquire_swfw_sync(&self, info: &PCIeInfo, mask: u32) -> Result<(), IxgbeDriverErr> {
        mac_acquire_swfw_sync_x540(info, mask)
    }

    fn mac_release_swfw_sync(&self, info: &PCIeInfo, mask: u32) -> Result<(), IxgbeDriverErr> {
        mac_release_swfw_sync_x540(info, mask)
    }

    fn mac_get_link_capabilities(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
    ) -> Result<(u32, bool), IxgbeDriverErr> {
        get_copper_link_capabilities(self, info, hw)
    }

    /// setup_mac_link_X540 - Sets the auto advertised capabilities
    fn mac_setup_link(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
        speed: u32,
        autoneg_wait_to_complete: bool,
    ) -> Result<(), IxgbeDriverErr> {
        self.phy_setup_link_speed(info, hw, speed, autoneg_wait_to_complete)
    }

    // PHY Operations

    /// Using copper phy
    fn phy_set_power(&self, info: &PCIeInfo, hw: &IxgbeHw, on: bool) -> Result<(), IxgbeDriverErr> {
        phy_set_power_x540(self, info, hw, on)
    }

    // EEPROM Operations

    /// Requires checking of EepromType to make sure that it is uninitialized beforehand
    fn eeprom_init_params(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
    ) -> Result<(), IxgbeDriverErr> {
        eeprom.eeprom_type = EepromType::IxgbeFlash;
        eeprom.semaphore_delay = 10;

        let eec = ixgbe_hw::read_reg(info, get_eec_offset(info.get_id())?)?;
        let eeprom_size = ((eec & IXGBE_EEC_SIZE) >> IXGBE_EEC_SIZE_SHIFT) as u16;
        eeprom.word_size = 1 << (eeprom_size + IXGBE_EEPROM_WORD_SIZE_SHIFT);

        Ok(())
    }

    fn eeprom_read(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
        offset: u16,
        data: &mut [u16],
    ) -> Result<(), IxgbeDriverErr> {
        ixgbe_operations::mac_swfw_sync_mut(self, info, IXGBE_GSSR_EEP_SM, 0, || {
            ixgbe_operations::read_eerd_buffer_generic(self, info, eeprom, offset, 1, data)
        })
    }

    fn eeprom_validate_checksum(&self, info: &PCIeInfo) -> Result<IxgbeEepromInfo, IxgbeDriverErr> {
        let mut eeprom = IxgbeEepromInfo {
            eeprom_type: EepromType::IxgbeEepromUninitialized,
            semaphore_delay: 0,
            word_size: 0,
            address_bits: 0,
            word_page_size: 0,
            ctrl_word_3: 0,
        };
        let mut data = [0; 1];
        self.eeprom_read(info, &mut eeprom, 0, &mut data)?;

        ixgbe_operations::mac_swfw_sync_mut(
            self,
            info,
            IXGBE_GSSR_EEP_SM,
            eeprom.semaphore_delay,
            || {
                let checksum = self.eeprom_calc_checksum(info, &mut eeprom)?;
                // Do not use self.read_eerd() because we do not want to
                // take the synchronization semaphore twice here.
                let mut read_checksum = [0; 1];
                ixgbe_operations::read_eerd_buffer_generic(
                    self,
                    info,
                    &mut eeprom,
                    IXGBE_EEPROM_CHECKSUM,
                    1,
                    &mut read_checksum,
                )?;

                // Verify read checksum from EEPROM is the same as
                // calculated checksum
                if read_checksum[0] != checksum {
                    log::error!("Invalid EEPROM checksum");
                    return Err(IxgbeDriverErr::EepromChecksum);
                }

                Ok(eeprom)
            },
        )
    }

    fn eeprom_calc_checksum(
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

/// Return `(mcft_size: u32, vft_size: u32, num_rar_entries: u32,
/// rx_pb_size: u32, max_rx_queues: u32, max_tx_queues: u32,
/// max_msix_vectors: u16, arc_subsystem_valid: bool)`.
#[allow(clippy::type_complexity)]
pub fn set_mac_val(
    info: &PCIeInfo,
) -> Result<(u32, u32, u32, u32, u32, u32, u16, bool), IxgbeDriverErr> {
    let arc_subsystem_valid =
        match ixgbe_hw::read_reg(info, IXGBE_FWSM_X540 & IXGBE_FWSM_MODE_MASK as usize) {
            Ok(val) => val != 0,
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
