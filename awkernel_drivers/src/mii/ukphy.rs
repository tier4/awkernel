use super::{Mii, MiiAttachArgs, MiiData, MiiError, MiiFlags, MiiPhy, MiiPhyData};

pub struct Ukphy {
    phy_data: MiiPhyData,
}

impl MiiPhy for Ukphy {
    fn service(&mut self, mii: &mut dyn Mii) -> Result<(), MiiError> {
        todo!()
    }

    fn status(&self, mii: &mut dyn Mii) -> u32 {
        todo!()
    }

    fn reset(&mut self, mii: &mut dyn Mii, mii_data: &mut MiiData) -> Result<(), MiiError> {
        crate::mii::physubr::phy_reset(mii, mii_data, self)
    }

    fn get_phy_data(&self) -> &MiiPhyData {
        &self.phy_data
    }

    fn get_phy_data_mut(&mut self) -> &mut MiiPhyData {
        &mut self.phy_data
    }
}

pub fn attach(
    mii: &mut dyn Mii,
    mii_data: &mut MiiData,
    args: MiiAttachArgs,
) -> Result<Ukphy, MiiError> {
    let mut ukphy = Ukphy {
        phy_data: MiiPhyData::new(mii_data, &args),
    };

    super::physubr::phy_dev_attach(mii, mii_data, MiiFlags::NOMANPAUSE, &mut ukphy)?;
    super::physubr::phy_set_media(mii, mii_data, &mut ukphy)?;

    loop {
        super::physubr::phy_tick(mii, mii_data, &mut ukphy)?;
        awkernel_lib::delay::wait_sec(1);
    }

    Ok(ukphy)
}
