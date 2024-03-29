use super::{Mii, MiiAttachArgs, MiiData, MiiError, MiiPhy, MiiPhyData};

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
        crate::mii::physubr::reset(mii, mii_data, self)
    }

    fn get_phy_data(&self) -> &MiiPhyData {
        &self.phy_data
    }

    fn get_phy_data_mut(&mut self) -> &mut MiiPhyData {
        &mut self.phy_data
    }
}

pub fn attach(mii: &mut dyn Mii, mii_data: &mut MiiData, args: MiiAttachArgs) -> Ukphy {
    Ukphy {
        phy_data: MiiPhyData::new(mii_data, &args),
    }
}
