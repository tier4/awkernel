use awkernel_lib::delay::{wait_microsec, wait_millisec};

use crate::pcie::{
    intel::igc::{
        igc_mac::igc_config_fc_after_link_up_generic,
        igc_phy::{igc_check_downshift_generic, igc_phy_has_link_generic},
    },
    PCIeInfo,
};

use super::{
    igc_base::{
        igc_acquire_phy_base, igc_init_hw_base, igc_power_down_phy_copper_base,
        igc_release_phy_base, IGC_RAR_ENTRIES_BASE,
    },
    igc_defines::*,
    igc_hw::{
        IgcHw, IgcMacOperations, IgcMediaType, IgcNvmOperations, IgcNvmType, IgcOperations,
        IgcPhyOperations, IgcPhyType,
    },
    igc_mac::{
        igc_check_alt_mac_addr_generic, igc_disable_pcie_master_generic,
        igc_get_auto_rd_done_generic, igc_get_speed_and_duplex_copper_generic,
        igc_put_hw_semaphore_generic, igc_setup_link_generic,
    },
    igc_nvm::{acquire_nvm, igc_read_nvm_eerd, igc_validate_nvm_checksum_generic},
    igc_phy::{
        igc_get_phy_id, igc_phy_hw_reset_generic, igc_power_up_phy_copper, igc_read_phy_reg_gpy,
        igc_write_phy_reg_gpy,
    },
    igc_regs::*,
    read_reg, write_flush, write_reg, IgcDriverErr,
};

pub(super) struct I225Flash;

impl IgcOperations for I225Flash {}

impl IgcMacOperations for I225Flash {
    fn init_params(&self, _info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_init_mac_params_i225(hw);
        Ok(())
    }

    fn check_for_link(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_check_for_link_i225(self, info, hw)
    }

    fn get_link_up_info(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
    ) -> Result<(IgcSpeed, IgcDuplex), IgcDriverErr> {
        igc_get_speed_and_duplex_copper_generic(info, hw)
    }

    fn reset_hw(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_reset_hw_i225(self, info, hw)
    }

    fn acquire_swfw_sync(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        mask: u16,
    ) -> Result<(), IgcDriverErr> {
        igc_acquire_swfw_sync_i225(info, hw, mask)
    }

    fn release_swfw_sync(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        mask: u16,
    ) -> Result<(), IgcDriverErr> {
        igc_release_swfw_sync_i225(info, hw, mask)
    }

    fn setup_link(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_setup_link_generic(self, info, hw)
    }

    fn init_hw(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_init_hw_base(self, info, hw)
    }
}

impl IgcPhyOperations for I225Flash {
    fn init_params(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_init_phy_params_i225(self, info, hw)
    }

    fn acquire(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_acquire_phy_base(self, info, hw)
    }

    fn release(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_release_phy_base(self, info, hw)
    }

    fn power_up(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_power_up_phy_copper(self, info, hw)
    }

    fn power_down(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_power_down_phy_copper_base(self, info, hw)
    }

    fn reset(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_phy_hw_reset_generic(self, info, hw)
    }

    fn read_reg(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        offset: u32,
    ) -> Result<u16, IgcDriverErr> {
        igc_read_phy_reg_gpy(self, info, hw, offset)
    }

    fn write_reg(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        offset: u32,
        data: u16,
    ) -> Result<(), IgcDriverErr> {
        igc_write_phy_reg_gpy(self, info, hw, offset, data)
    }
}

impl IgcNvmOperations for I225Flash {
    fn acquire(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_acquire_swfw_sync_i225(info, hw, IGC_SWFW_EEP_SM)
    }

    fn release(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_release_swfw_sync_i225(info, hw, IGC_SWFW_EEP_SM)
    }

    fn init_params(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_init_nvm_params_i225(info, hw)?;
        hw.nvm.nvm_type = IgcNvmType::FlashHw;
        Ok(())
    }

    fn validate(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_validate_nvm_checksum_i225(self, info, hw)
    }

    fn read(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        offset: u16,
        words: u16,
        data: &mut [u16],
    ) -> Result<(), IgcDriverErr> {
        igc_read_nvm_srrd_i225(self, info, hw, offset, words, data)
    }

    fn write(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        offset: u16,
        words: u16,
        data: &[u16],
    ) -> Result<(), IgcDriverErr> {
        igc_write_nvm_srwr_i225(self, info, hw, offset, words, data)
    }
}

pub(super) struct I225NoFlash;

impl IgcOperations for I225NoFlash {}

impl IgcMacOperations for I225NoFlash {
    fn init_params(&self, _info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_init_mac_params_i225(hw);
        Ok(())
    }

    fn check_for_link(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_check_for_link_i225(self, info, hw)
    }

    fn get_link_up_info(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
    ) -> Result<(IgcSpeed, IgcDuplex), IgcDriverErr> {
        igc_get_speed_and_duplex_copper_generic(info, hw)
    }

    fn reset_hw(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_reset_hw_i225(self, info, hw)
    }

    fn acquire_swfw_sync(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        mask: u16,
    ) -> Result<(), IgcDriverErr> {
        igc_acquire_swfw_sync_i225(info, hw, mask)
    }

    fn release_swfw_sync(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        mask: u16,
    ) -> Result<(), IgcDriverErr> {
        igc_release_swfw_sync_i225(info, hw, mask)
    }

    fn setup_link(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_setup_link_generic(self, info, hw)
    }

    fn init_hw(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_init_hw_base(self, info, hw)
    }
}

impl IgcPhyOperations for I225NoFlash {
    fn init_params(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_init_phy_params_i225(self, info, hw)
    }

    fn acquire(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_acquire_phy_base(self, info, hw)
    }

    fn release(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_release_phy_base(self, info, hw)
    }

    fn power_up(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_power_up_phy_copper(self, info, hw)
    }

    fn power_down(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_power_down_phy_copper_base(self, info, hw)
    }

    fn reset(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_phy_hw_reset_generic(self, info, hw)
    }

    fn read_reg(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        offset: u32,
    ) -> Result<u16, IgcDriverErr> {
        igc_read_phy_reg_gpy(self, info, hw, offset)
    }

    fn write_reg(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        offset: u32,
        data: u16,
    ) -> Result<(), IgcDriverErr> {
        igc_write_phy_reg_gpy(self, info, hw, offset, data)
    }
}

impl IgcNvmOperations for I225NoFlash {
    fn acquire(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_acquire_swfw_sync_i225(info, hw, IGC_SWFW_EEP_SM)
    }

    fn release(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_release_swfw_sync_i225(info, hw, IGC_SWFW_EEP_SM)
    }

    fn init_params(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_init_nvm_params_i225(info, hw)?;
        hw.nvm.nvm_type = IgcNvmType::Invm;
        Ok(())
    }

    fn validate(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        Ok(())
    }
}

pub(super) fn igc_get_flash_presence_i225(info: &PCIeInfo) -> Result<bool, IgcDriverErr> {
    let eec = read_reg(info, IGC_EECD)?;
    Ok(eec & IGC_EECD_FLASH_DETECTED_I225 != 0)
}

/// Reset hardware
/// This resets the hardware into a known state.
fn igc_reset_hw_i225(
    i225: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    // Prevent the PCI-E bus from sticking if there is no TLP connection
    // on the last TLP read/write transaction when MAC is reset.
    igc_disable_pcie_master_generic(info)?;

    write_reg(info, IGC_IMC, 0xffffffff)?;

    write_reg(info, IGC_RCTL, 0)?;
    write_reg(info, IGC_TCTL, IGC_TCTL_PSP)?;
    write_flush(info)?;

    wait_millisec(10);

    let ctrl = read_reg(info, IGC_CTRL)?;
    write_reg(info, IGC_CTRL, ctrl | IGC_CTRL_DEV_RST)?;

    igc_get_auto_rd_done_generic(info)?;

    // Clear any pending interrupt events.
    write_reg(info, IGC_IMC, 0xffffffff)?;
    read_reg(info, IGC_ICR)?;

    // Install any alternate MAC address into RAR0
    igc_check_alt_mac_addr_generic(i225, info, hw)?;

    Ok(())
}

/// Acquire the HW semaphore to access the PHY or NVM
fn igc_get_hw_semaphore_i225(info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
    let mut swsm;
    let timeout = hw.nvm.word_size + 1;
    let mut i = 0;

    // Get the SW semaphore
    while i < timeout {
        swsm = read_reg(info, IGC_SWSM)?;
        if swsm & IGC_SWSM_SMBI == 0 {
            break;
        }

        wait_microsec(50);
        i += 1;
    }

    if i == timeout {
        // In rare circumstances, the SW semaphore may already be held
        // unintentionally. Clear the semaphore once before giving up.
        if hw.dev_spec.clear_semaphore_once {
            hw.dev_spec.clear_semaphore_once = false;
            igc_put_hw_semaphore_generic(info)?;

            i = 0;
            while i < timeout {
                swsm = read_reg(info, IGC_SWSM)?;
                if swsm & IGC_SWSM_SMBI == 0 {
                    break;
                }

                wait_microsec(50);
                i += 1;
            }
        }

        // If we do not have the semaphore here, we have to give up.
        if i == timeout {
            log::debug!("Driver can't access device - SMBI bit is set.");
            return Err(IgcDriverErr::NVM);
        }
    }

    // Get the FW semaphore.
    i = 0;
    while i < timeout {
        swsm = read_reg(info, IGC_SWSM)?;
        write_reg(info, IGC_SWSM, swsm | IGC_SWSM_SWESMBI)?;

        // Semaphore acquired if bit latched
        if read_reg(info, IGC_SWSM)? & IGC_SWSM_SWESMBI != 0 {
            break;
        }

        wait_microsec(50);
        i += 1;
    }

    if i == timeout {
        // Release semaphores
        igc_put_hw_semaphore_generic(info)?;
        log::debug!("Driver can't access the NVM");
        return Err(IgcDriverErr::NVM);
    }

    Ok(())
}

/// Acquire the SW/FW semaphore to access the PHY or NVM.  The mask
/// will also specify which port we're acquiring the lock for.
fn igc_acquire_swfw_sync_i225(
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    mask: u16,
) -> Result<(), IgcDriverErr> {
    let swmask = mask as u32;
    let fwmask = (mask as u32) << 16;
    let timeout = 200;

    for _ in 0..timeout {
        igc_get_hw_semaphore_i225(info, hw)?;

        let mut swfw_sync = read_reg(info, IGC_SW_FW_SYNC)?;
        if swfw_sync & (fwmask | swmask) == 0 {
            swfw_sync |= swmask;
            let result = write_reg(info, IGC_SW_FW_SYNC, swfw_sync);
            igc_put_hw_semaphore_generic(info)?;
            return result;
        }

        // Firmware currently using resource (fwmask)
        // or other software thread using resource (swmask)
        igc_put_hw_semaphore_generic(info)?;
        wait_millisec(5);
    }

    // timeout
    Err(IgcDriverErr::SwfwSync)
}

/// Release the SW/FW semaphore used to access the PHY or NVM.  The mask
/// will also specify which port we're releasing the lock for.
fn igc_release_swfw_sync_i225(
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    mask: u16,
) -> Result<(), IgcDriverErr> {
    while igc_get_hw_semaphore_i225(info, hw).is_err() {}

    let mut swfw_sync = read_reg(info, IGC_SW_FW_SYNC)?;
    swfw_sync &= !(mask as u32);
    write_reg(info, IGC_SW_FW_SYNC, swfw_sync)?;

    igc_put_hw_semaphore_generic(info)?;

    Ok(())
}

fn igc_init_mac_params_i225(hw: &mut IgcHw) {
    // Set media type
    hw.phy.media_type = IgcMediaType::Copper;
    // Set mta register count
    hw.mac.mta_reg_count = 128;
    // Set rar entry count
    hw.mac.rar_entry_count = IGC_RAR_ENTRIES_BASE;

    // Allow a single clear of the SW semaphore on I225
    hw.dev_spec.clear_semaphore_once = true;

    // Set if part includes ASF firmware
    hw.mac.asf_firmware_present = true;
}

fn igc_init_nvm_params_i225(info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
    let nvm = &mut hw.nvm;
    let eecd = read_reg(info, IGC_EECD)?;

    // Added to a constant, "size" becomes the left-shift value
    // for setting word_size.
    // `+ NVM_WORD_SIZE_BASE_SHIFT`

    let size =
        ((eecd & IGC_EECD_SIZE_EX_MASK) >> IGC_EECD_SIZE_EX_SHIFT) + NVM_WORD_SIZE_BASE_SHIFT;

    // Just in case size is out of range, cap it to the largest
    // EEPROM size supported.
    let size = if size > 15 { 15 } else { size };

    nvm.word_size = 1 << size;
    nvm.opcode_bits = 8;
    nvm.delay_usec = 1;
    nvm.nvm_type = IgcNvmType::EepromSpi;

    nvm.page_size = if eecd & IGC_EECD_ADDR_BITS != 0 {
        32
    } else {
        8
    };

    nvm.address_bits = if eecd & IGC_EECD_ADDR_BITS != 0 {
        16
    } else {
        8
    };

    if nvm.word_size == 1 << 15 {
        nvm.page_size = 128;
    }

    // The original code uses `igc_get_flash_presence_i225()`
    // to check if flash is present and to initialize VNM operations.
    // However, in Awkernel, we don't use it here,
    // but it should be used when creating an instance of `IgcOperations`.

    Ok(())
}

fn igc_init_phy_params_i225(
    ops: &dyn IgcPhyOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    let phy = &mut hw.phy;

    if phy.media_type != IgcMediaType::Copper {
        phy.phy_type = IgcPhyType::None;
        return Ok(());
    }

    phy.autoneg_mask = AUTONEG_ADVERTISE_SPEED_DEFAULT_2500;
    phy.reset_delay_us = 100;

    // Make sure the PHY is in a good state. Several people have reported
    // firmware leaving the PHY's page select register set to something
    // other than the default of zero, which causes the PHY ID read to
    // access something other than the intended register.
    ops.reset(info, hw)?;

    igc_get_phy_id(ops, info, hw)?;
    hw.phy.phy_type = IgcPhyType::I225;

    Ok(())
}

/// Calculates the EEPROM checksum by reading/adding each word of the EEPROM
/// and then verifies that the sum of the EEPROM is equal to 0xBABA.
fn igc_validate_nvm_checksum_i225(
    ops: &dyn IgcNvmOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    acquire_nvm(ops, info, hw, |_, info, hw| {
        igc_validate_nvm_checksum_generic(info, hw, igc_read_nvm_eerd)?;

        Ok(())
    })?;

    Ok(())
}

/// Reads a 16 bit word from the Shadow Ram using the EERD register.
/// Uses necessary synchronization semaphores.
fn igc_read_nvm_srrd_i225(
    ops: &dyn IgcNvmOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    offset: u16,
    words: u16,
    data: &mut [u16],
) -> Result<(), IgcDriverErr> {
    // We cannot hold synchronization semaphores for too long,
    // because of forceful takeover procedure. However it is more efficient
    // to read in bursts than synchronizing access for each word.
    for i in (0..words).step_by(IGC_EERD_EEWR_MAX_COUNT as usize) {
        let count = if (words - i) / IGC_EERD_EEWR_MAX_COUNT > 0 {
            IGC_EERD_EEWR_MAX_COUNT
        } else {
            words - i
        };

        acquire_nvm(ops, info, hw, |_ops, info, hw| {
            igc_read_nvm_eerd(info, hw, offset, count, &mut data[i as usize..])
        })?;
    }

    Ok(())
}

/// Writes data to Shadow RAM at offset using EEWR register.
///
/// If igc_update_nvm_checksum is not called after this function , the
/// data will not be committed to FLASH and also Shadow RAM will most likely
/// contain an invalid checksum.
///
/// If error code is returned, data and Shadow RAM may be inconsistent - buffer
/// partially written.
fn igc_write_nvm_srwr_i225(
    ops: &dyn IgcNvmOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    offset: u16,
    words: u16,
    data: &[u16],
) -> Result<(), IgcDriverErr> {
    // We cannot hold synchronization semaphores for too long,
    // because of forceful takeover procedure. However it is more efficient
    // to write in bursts than synchronizing access for each word.
    for i in (0..words).step_by(IGC_EERD_EEWR_MAX_COUNT as usize) {
        let count = if (words - i) / IGC_EERD_EEWR_MAX_COUNT > 0 {
            IGC_EERD_EEWR_MAX_COUNT
        } else {
            words - i
        };

        acquire_nvm(ops, info, hw, |_ops, info, hw| {
            igc_write_nvm_srwr(info, hw, offset, count, &data[i as usize..])
        })?;
    }

    Ok(())
}

/// Writes data to Shadow Ram at offset using EEWR register.
///
/// If igc_update_nvm_checksum is not called after this function , the
/// Shadow Ram will most likely contain an invalid checksum.
fn igc_write_nvm_srwr(
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    offset: u16,
    words: u16,
    data: &[u16],
) -> Result<(), IgcDriverErr> {
    let attempts = 100000;

    // A check for invalid values:  offset too large, too many words,
    // too many words for the offset, and not enough words.
    if offset >= hw.nvm.word_size || words > (hw.nvm.word_size - offset) || words == 0 {
        return Err(IgcDriverErr::NVM);
    }

    'outer: for i in 0..words {
        let eewr = (((offset + i) as u32) << IGC_NVM_RW_ADDR_SHIFT)
            | ((data[i as usize] as u32) << IGC_NVM_RW_REG_DATA)
            | IGC_NVM_RW_REG_START;

        write_reg(info, IGC_SRWR, eewr)?;

        for _ in 0..attempts {
            if IGC_NVM_RW_REG_DONE & read_reg(info, IGC_SRWR)? != 0 {
                continue 'outer;
            }
            wait_microsec(5);
        }

        return Err(IgcDriverErr::NVM);
    }

    Ok(())
}

/// igc_check_for_link_i225 - Check for link
/// @hw: pointer to the HW structure
///
/// Checks to see of the link status of the hardware has changed.  If a
/// change in link status has been detected, then we read the PHY registers
/// to get the current speed/duplex if link exists.
fn igc_check_for_link_i225(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    struct IgcSetLtrI225;
    let mut link = false;

    // To implement goto statements in Rust, we use a loop with a break statement.
    #[allow(clippy::never_loop)]
    loop {
        // We only want to go out to the PHY registers to see if
        // Auto-Neg has completed and/or if our link status has
        // changed.  The get_link_status flag is set upon receiving
        // a Link Status Change or Rx Sequence Error interrupt.
        if !hw.mac.get_link_status {
            igc_set_ltr_i225(ops, info, hw, link)?;
            return Ok(());
        }

        // First we want to see if the MII Status Register reports
        // link.  If so, then we want to get the current speed/duplex
        // of the PHY.
        link = igc_phy_has_link_generic(ops, info, hw, 1, 0)?;

        if !link {
            // No link detected
            break;
        }

        // Note: The original code calls `igc_phy_has_link_generic()` again.

        // First we want to see if the MII Status Register reports
        // link.  If so, then we want to get the current speed/duplex
        // of the PHY.
        link = igc_phy_has_link_generic(ops, info, hw, 1, 0)?;

        if !link {
            // No link detected
            break;
        }

        hw.mac.get_link_status = false;

        // Check if there was DownShift, must be checked
        // immediately after link-up
        let _ = igc_check_downshift_generic(hw);

        // If we are forcing speed/duplex, then we simply return since
        // we have already determined whether we have link or not.
        if !hw.mac.autoneg {
            break;
        }

        // Auto-Neg is enabled.  Auto Speed Detection takes care
        // of MAC speed/duplex configuration.  So we only need to
        // configure Collision Distance in the MAC.
        ops.config_collision_dist(info, hw)?;

        // Configure Flow Control now that Auto-Neg has completed.
        // First, we need to restore the desired flow control
        // settings because we may have had to re-autoneg with a
        // different link partner.
        igc_config_fc_after_link_up_generic(ops, info, hw)?;

        break;
    }

    // Now that we are aware of our link settings, we can set the LTR
    // thresholds.
    igc_set_ltr_i225(ops, info, hw, link)
}

/// igc_set_ltr_i225 - Set Latency Tolerance Reporting thresholds.
/// @hw: pointer to the HW structure
/// @link: bool indicating link status
///
/// Set the LTR thresholds based on the link speed (Mbps), EEE, and DMAC
/// settings, otherwise specify that there is no LTR requirement.
fn igc_set_ltr_i225(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    link: bool,
) -> Result<(), IgcDriverErr> {
    // If we do not have link, LTR thresholds are zero.
    if link {
        let (speed, _duplex) = ops.get_link_up_info(info, hw)?;

        // Check if using copper interface with EEE enabled or if the
        // link speed is 10 Mbps.
        let tw_system = if hw.phy.media_type == IgcMediaType::Copper
            && !hw.dev_spec.eee_disable
            && speed != IgcSpeed::Speed10
        {
            // EEE enabled, so send LTRMAX threshold.
            let ltrc = read_reg(info, IGC_LTRC)? | IGC_LTRC_EEEMS_EN;
            write_reg(info, IGC_LTRC, ltrc)?;

            // Calculate tw_system (nsec).
            if speed == IgcSpeed::Speed100 {
                ((read_reg(info, IGC_EEE_SU)? & IGC_TW_SYSTEM_100_MASK) >> IGC_TW_SYSTEM_100_SHIFT)
                    * 500
            } else {
                (read_reg(info, IGC_EEE_SU)? & IGC_TW_SYSTEM_1000_MASK) * 500
            }
        } else {
            0
        };

        // Get the Rx packet buffer size.
        let size = read_reg(info, IGC_RXPBS)? & IGC_RXPBS_SIZE_I225_MASK;

        // Calculations vary based on DMAC settings.
        let size = if read_reg(info, IGC_DMACR)? & IGC_DMACR_DMAC_EN != 0 {
            size.checked_sub(
                ((read_reg(info, IGC_DMACR)? & IGC_DMACR_DMACTHR_MASK) >> IGC_DMACR_DMACTHR_SHIFT)
                    * 1024
                    * 8,
            )
            .ok_or(IgcDriverErr::Config)?
        } else {
            // Convert size to bytes, subtract the MTU, and then
            // convert the size to bits.
            (size * 1024)
                .checked_sub(hw.dev_spec.mtu * 8)
                .ok_or(IgcDriverErr::Config)?
        };

        // Calculate the thresholds. Since speed is in Mbps, simplify
        // the calculation by multiplying size/speed by 1000 for result
        // to be in nsec before dividing by the scale in nsec. Set the
        // scale such that the LTR threshold fits in the register.
        let ltr_min = (1000 * size as u32) / speed as u32;
        let ltr_max = ltr_min + tw_system;
        let scale_min = if ltr_min / 1024 < 1024 {
            IGC_LTRMINV_SCALE_1024
        } else {
            IGC_LTRMINV_SCALE_32768
        };
        let scale_max = if ltr_max / 1024 < 1024 {
            IGC_LTRMAXV_SCALE_1024
        } else {
            IGC_LTRMAXV_SCALE_32768
        };
        let ltr_min = ltr_min
            / if scale_min == IGC_LTRMINV_SCALE_1024 {
                1024
            } else {
                32768
            };
        let ltr_max = ltr_max
            / if scale_max == IGC_LTRMAXV_SCALE_1024 {
                1024
            } else {
                32768
            };

        // Only write the LTR thresholds if they differ from before.
        let ltrv = read_reg(info, IGC_LTRMINV)?;
        if ltr_min != (ltrv & IGC_LTRMINV_LTRV_MASK) {
            let ltrv = IGC_LTRMINV_LSNP_REQ | ltr_min | (scale_min << IGC_LTRMINV_SCALE_SHIFT);
            write_reg(info, IGC_LTRMINV, ltrv)?;
        }

        let ltrv = read_reg(info, IGC_LTRMAXV)?;
        if ltr_max != (ltrv & IGC_LTRMAXV_LTRV_MASK) {
            let ltrv = ltr_max | (scale_max << IGC_LTRMAXV_SCALE_SHIFT);
            write_reg(info, IGC_LTRMAXV, ltrv)?;
        }
    }

    Ok(())
}
