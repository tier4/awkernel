use super::{Mii, MiiData, MiiError, MiiFlags, MiiPhy};

pub fn dev_attach(
    mii: &mut dyn Mii,
    mii_data: &mut MiiData,
    flags: MiiFlags,
    phy: &mut dyn MiiPhy,
) -> Result<(), MiiError> {
    let mut phy_data = phy.get_phy_data_mut();

    phy_data.flags |= flags;

    Ok(())
}
