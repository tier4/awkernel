use awkernel_lib::delay::{wait_microsec, wait_millisec};

use crate::pcie::PCIeInfo;

use super::{
    igc_defines::*,
    igc_hw::{IgcHw, IgcMacOperations, IgcNvmOperations, IgcOperations, IgcPhyOperations},
    igc_mac::{
        igc_check_alt_mac_addr_generic, igc_disable_pcie_master_generic,
        igc_get_auto_rd_done_generic, igc_put_hw_semaphore_generic,
    },
    igc_regs::*,
    read_reg, write_flush, write_reg, IgcDriverErr,
};

pub(super) struct I225Flash;

impl IgcOperations for I225Flash {}

impl IgcMacOperations for I225Flash {
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
}

impl IgcPhyOperations for I225Flash {}

impl IgcNvmOperations for I225Flash {
    fn acquire(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_acquire_swfw_sync_i225(info, hw, IGC_SWFW_EEP_SM)
    }

    fn release(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_release_swfw_sync_i225(info, hw, IGC_SWFW_EEP_SM)
    }
}

pub(super) struct I225NoFlash;

impl IgcOperations for I225NoFlash {}

impl IgcMacOperations for I225NoFlash {
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
}

impl IgcPhyOperations for I225NoFlash {}

impl IgcNvmOperations for I225NoFlash {
    fn acquire(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_acquire_swfw_sync_i225(info, hw, IGC_SWFW_EEP_SM)
    }

    fn release(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_release_swfw_sync_i225(info, hw, IGC_SWFW_EEP_SM)
    }
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
            write_reg(info, IGC_SW_FW_SYNC, swfw_sync)?;
            return Ok(());
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
