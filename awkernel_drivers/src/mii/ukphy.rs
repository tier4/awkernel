use crate::{
    if_media::{
        IFM_1000_T, IFM_100_T4, IFM_100_TX, IFM_10_T, IFM_ETH_MASTER, IFM_FDX, IFM_HDX, IFM_LOOP,
        IFM_NONE,
    },
    mii::*,
};

use self::physubr::phy_update;

use super::physubr::TickReturn;

pub struct Ukphy {
    phy_data: MiiPhyData,
}

impl MiiPhy for Ukphy {
    fn service(
        &mut self,
        mii: &mut dyn Mii,
        mii_data: &mut MiiData,
        cmd: MiiPhyCmd,
    ) -> Result<(), MiiError> {
        match cmd {
            MiiPhyCmd::PollStat => (),
            MiiPhyCmd::MediaChg => super::physubr::phy_set_media(mii, mii_data, self)?,
            MiiPhyCmd::Tick => {
                if super::physubr::phy_tick(mii, mii_data, self)? == TickReturn::JustReturn {
                    return Ok(());
                }
            }
        }

        // Update the media status.
        self.status(mii, mii_data)?;

        // Callback if something changed.
        phy_update(mii, mii_data, self, cmd)?;

        Ok(())
    }

    fn status(&self, mii: &mut dyn Mii, mii_data: &mut MiiData) -> Result<(), MiiError> {
        mii_data.media_status = Media::new(IFM_AVALID);
        mii_data.media_active = Media::new(IFM_ETHER);

        let phy_data = self.get_phy_data();

        let bmsr = mii.read_reg(phy_data.phy, MII_BMSR)? | mii.read_reg(phy_data.phy, MII_BMSR)?;
        if bmsr & BMSR_LINK != 0 {
            mii_data.media_status.insert(IFM_ACTIVE);
        }

        let bmcr = mii.read_reg(phy_data.phy, MII_BMCR)?;
        if bmcr & BMCR_ISO != 0 {
            mii_data.media_active.insert(IFM_NONE);
            mii_data.media_status = Media::new(0);
            return Ok(());
        }

        if bmcr & BMCR_LOOP != 0 {
            mii_data.media_active.insert(IFM_LOOP);
        }

        if bmcr & BMCR_AUTOEN != 0 {
            // NWay autonegotiation takes the highest-order common
            // bit of the ANAR and ANLPAR (i.e. best media advertised
            // both by us and our link partner).
            if bmsr & BMSR_ACOMP == 0 {
                // Erg, still trying, I guess...
                mii_data.media_active.insert(IFM_NONE);
                return Ok(());
            }

            let anlpar =
                mii.read_reg(phy_data.phy, MII_ANAR)? & mii.read_reg(phy_data.phy, MII_ANLPAR)?;

            let (gtcr, gtsr) = if phy_data.flags.contains(MiiFlags::HAVE_GTCR)
                && (phy_data.extcapabilities & (EXTSR_1000THDX | EXTSR_1000TFDX)) != 0
            {
                (
                    mii.read_reg(phy_data.phy, MII_100T2CR)?,
                    mii.read_reg(phy_data.phy, MII_100T2SR)?,
                )
            } else {
                (0, 0)
            };

            if gtcr & GTCR_ADV_1000TFDX != 0 && gtsr & GTSR_LP_1000TFDX != 0 {
                mii_data.media_active.insert(IFM_1000_T | IFM_FDX);
            } else if gtcr & GTCR_ADV_1000THDX != 0 && gtsr & GTSR_LP_1000THDX != 0 {
                mii_data.media_active.insert(IFM_1000_T | IFM_HDX);
            } else if anlpar & ANLPAR_TX_FD != 0 {
                mii_data.media_active.insert(IFM_100_TX | IFM_FDX);
            } else if anlpar & ANLPAR_T4 != 0 {
                mii_data.media_active.insert(IFM_100_T4 | IFM_HDX);
            } else if anlpar & ANLPAR_TX != 0 {
                mii_data.media_active.insert(IFM_100_TX | IFM_HDX);
            } else if anlpar & ANLPAR_10_FD != 0 {
                mii_data.media_active.insert(IFM_10_T | IFM_FDX);
            } else if anlpar & ANLPAR_10 != 0 {
                mii_data.media_active.insert(IFM_10_T | IFM_HDX);
            } else {
                mii_data.media_active.insert(IFM_NONE);
            }

            if mii_data.media_active.contains(IFM_1000_T) && gtsr & GTSR_MS_RES != 0 {
                mii_data.media_active.insert(IFM_ETH_MASTER);
            }

            if mii_data.media_active.contains(IFM_FDX) {
                mii_data
                    .media_active
                    .insert(super::physubr::phy_flowstatus(mii, self)?);
            }
        } else {
            let Some(ife) = mii_data.media.get_current() else {
                return Ok(());
            };

            mii_data.media_active = ife.media;
        }

        Ok(())
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
) -> Result<Box<dyn MiiPhy + Send + Sync>, MiiError> {
    let mut ukphy = Ukphy {
        phy_data: MiiPhyData::new(mii_data, &args),
    };

    super::physubr::phy_dev_attach(mii, mii_data, MiiFlags::NOMANPAUSE, &mut ukphy)?;
    super::physubr::phy_set_media(mii, mii_data, &mut ukphy)?;

    Ok(Box::new(ukphy))
}
