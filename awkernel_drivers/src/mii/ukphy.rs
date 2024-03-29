use super::{Mii, MiiAttachArgs, MiiData, MiiError, MiiPhy};

pub struct Ukphy {
    args: MiiAttachArgs,
}

impl MiiPhy for Ukphy {
    fn service(&mut self, mii: &mut dyn Mii) -> Result<(), MiiError> {
        todo!()
    }

    fn status(&self, mii: &mut dyn Mii) -> u32 {
        todo!()
    }

    fn reset(&mut self, mii: &mut dyn Mii) -> Result<(), MiiError> {
        todo!()
    }

    fn get_args(&self) -> &MiiAttachArgs {
        &self.args
    }

    fn get_args_mut(&mut self) -> &mut MiiAttachArgs {
        &mut self.args
    }
}

pub fn attach(mii: &mut dyn Mii, mii_data: &mut MiiData, args: MiiAttachArgs) -> Ukphy {
    Ukphy { args }
}
