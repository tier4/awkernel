use awkernel_lib::delay::wait_microsec;

use crate::pcie::PCIeInfo;

use super::{
    igc_defines::{
        IGC_NVM_POLL_READ, IGC_NVM_RW_ADDR_SHIFT, IGC_NVM_RW_REG_DATA, IGC_NVM_RW_REG_DONE,
        IGC_NVM_RW_REG_START, NVM_CHECKSUM_REG, NVM_SUM,
    },
    igc_hw::{IgcHw, IgcNvmOperations},
    igc_regs::{IGC_EERD, IGC_EEWR},
    read_reg, write_reg, IgcDriverErr,
};

/// Calculates the EEPROM checksum by reading/adding each word of the EEPROM
/// and then verifies that the sum of the EEPROM is equal to 0xBABA.
pub(super) fn igc_validate_nvm_checksum_generic<F>(
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    mut read: F,
) -> Result<(), IgcDriverErr>
where
    F: FnMut(&mut PCIeInfo, &mut IgcHw, u16, u16, &mut [u16]) -> Result<(), IgcDriverErr>,
{
    let mut checksum = 0;

    for i in 0..NVM_CHECKSUM_REG + 1 {
        let mut nvm_data = [0];
        read(info, hw, i, 1, &mut nvm_data)?;
        checksum += nvm_data[0];
    }

    if checksum != NVM_SUM {
        log::error!("igc: NVM Checksum Invalid");
        return Err(IgcDriverErr::NVM);
    }

    Ok(())
}

pub(super) fn acquire_nvm<F, R>(
    ops: &dyn IgcNvmOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    f: F,
) -> Result<R, IgcDriverErr>
where
    F: Fn(&dyn IgcNvmOperations, &mut PCIeInfo, &mut IgcHw) -> Result<R, IgcDriverErr>,
{
    IgcNvmOperations::acquire(ops, info, hw)?;
    let result = f(ops, info, hw);
    IgcNvmOperations::release(ops, info, hw)?;
    result
}

/// Reads a 16 bit word from the EEPROM using the EERD register.
pub(super) fn igc_read_nvm_eerd(
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    offset: u16,
    words: u16,
    data: &mut [u16],
) -> Result<(), IgcDriverErr> {
    // A check for invalid values:  offset too large, too many words,
    // too many words for the offset, and not enough words.
    if offset >= hw.nvm.word_size || words > (hw.nvm.word_size - offset) || words == 0 {
        return Err(IgcDriverErr::NVM);
    }

    for i in 0..words {
        let eerd = ((offset + i) << IGC_NVM_RW_ADDR_SHIFT) as u32 + IGC_NVM_RW_REG_START;
        write_reg(info, IGC_EERD, eerd)?;
        igc_poll_eerd_eewr_done(info, IGC_NVM_POLL_READ)?;

        data[i as usize] = (read_reg(info, IGC_EERD)? >> IGC_NVM_RW_REG_DATA) as u16;
    }

    Ok(())
}

/// Polls the EEPROM status bit for either read or write completion based
/// upon the value of 'ee_reg'.
fn igc_poll_eerd_eewr_done(info: &mut PCIeInfo, ee_reg: u32) -> Result<(), IgcDriverErr> {
    let attempts = 100000;

    for _ in 0..attempts {
        let reg = if ee_reg == IGC_NVM_POLL_READ {
            read_reg(info, IGC_EERD)?
        } else {
            read_reg(info, IGC_EEWR)?
        };

        if reg & IGC_NVM_RW_REG_DONE != 0 {
            return Ok(());
        }

        wait_microsec(5);
    }

    Err(IgcDriverErr::NVM)
}
