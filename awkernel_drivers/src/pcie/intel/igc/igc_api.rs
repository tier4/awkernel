use crate::pcie::PCIeInfo;

use super::{
    igc_get_flash_presence_i225,
    igc_hw::{IgcHw, IgcMacOperations, IgcNvmOperations, IgcPhyOperations},
    I225Flash, I225NoFlash, IgcDriverErr, IgcMacType, IgcOperations,
};

use alloc::boxed::Box;

// This function sets the mac type of the adapter based on the
// device ID stored in the hw structure.
// MUST BE FIRST FUNCTION CALLED (explicitly or through
// `igc_setup_init_funcs()`).
pub(super) fn igc_set_mac_type(igc_hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
    use super::igc_hw::*;

    match igc_hw.device_id {
        PCI_PRODUCT_INTEL_I220_V
        | PCI_PRODUCT_INTEL_I221_V
        | PCI_PRODUCT_INTEL_I225_BLANK_NVM
        | PCI_PRODUCT_INTEL_I225_I
        | PCI_PRODUCT_INTEL_I225_IT
        | PCI_PRODUCT_INTEL_I225_K
        | PCI_PRODUCT_INTEL_I225_K2
        | PCI_PRODUCT_INTEL_I225_LM
        | PCI_PRODUCT_INTEL_I225_LMVP
        | PCI_PRODUCT_INTEL_I225_V
        | PCI_PRODUCT_INTEL_I226_BLANK_NVM
        | PCI_PRODUCT_INTEL_I226_IT
        | PCI_PRODUCT_INTEL_I226_LM
        | PCI_PRODUCT_INTEL_I226_K
        | PCI_PRODUCT_INTEL_I226_V => {
            igc_hw.mac.mac_type = IgcMacType::I225;
        }
        _ => return Err(IgcDriverErr::MacInit),
    };

    Ok(())
}

pub(super) fn igc_setup_init_funcs(
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<Box<dyn IgcOperations + Send + Sync>, IgcDriverErr> {
    let ops: Box<dyn IgcOperations + Send + Sync> = match hw.mac.mac_type {
        IgcMacType::I225 => {
            if igc_get_flash_presence_i225(&info)? {
                Box::new(I225Flash)
            } else {
                Box::new(I225NoFlash)
            }
        }
        IgcMacType::Undefined => {
            log::warn!("Unsupported MAC type: {:?}", hw.mac.mac_type);
            return Err(IgcDriverErr::Config);
        }
    };

    IgcMacOperations::init_params(ops.as_ref(), info, hw)?;
    IgcNvmOperations::init_params(ops.as_ref(), info, hw)?;
    IgcPhyOperations::init_params(ops.as_ref(), info, hw)?;

    Ok(ops)
}
