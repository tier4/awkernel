use awkernel_lib::delay::wait_millisec;

use crate::pcie::PCIeInfo;

use super::{
    igc_defines::*,
    igc_hw::{IgcHw, IgcMacOperations, IgcNvmOperations, IgcOperations, IgcPhyOperations},
    igc_mac::{
        igc_check_alt_mac_addr_generic, igc_disable_pcie_master_generic,
        igc_get_auto_rd_done_generic,
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
}

impl IgcPhyOperations for I225Flash {}
impl IgcNvmOperations for I225Flash {}

pub(super) struct I225NoFlash;

impl IgcOperations for I225NoFlash {}

impl IgcMacOperations for I225NoFlash {
    fn reset_hw(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        igc_reset_hw_i225(self, info, hw)
    }
}

impl IgcPhyOperations for I225NoFlash {}
impl IgcNvmOperations for I225NoFlash {}

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
