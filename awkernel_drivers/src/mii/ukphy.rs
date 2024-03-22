use super::*;
use crate::if_media::*;

pub struct Ukphy {
    ma: MiiAttachArgs,
}

impl MiiPhy for Ukphy {
    fn service(&self, parent: &mut dyn Mii, ma: &mut MiiAttachArgs, opcode: MiiOpCode) {
        // TODO: Implement the service routine of the PHY.

        // 143         struct ifmedia_entry *ife = mii->mii_media.ifm_cur;
        // 144         int reg;
        // 145
        // 146         if ((sc->mii_dev.dv_flags & DVF_ACTIVE) == 0)
        // 147                 return (ENXIO);
        // 148

        match opcode {
            MiiOpCode::PollStatus => {
                // 149         switch (cmd) {
                // 150         case MII_POLLSTAT:
                // 151                 /*
                // 152                  * If we're not polling our PHY instance, just return.
                // 153                  */
                // 154                 if (IFM_INST(ife->ifm_media) != sc->mii_inst)
                // 155                         return (0);
                // 156                 break;
                // 157
            }
            MiiOpCode::MediaChange => {
                // 158         case MII_MEDIACHG:
                // 159                 /*
                // 160                  * If the media indicates a different PHY instance,
                // 161                  * isolate ourselves.
                // 162                  */
                // 163                 if (IFM_INST(ife->ifm_media) != sc->mii_inst) {
                // 164                         reg = PHY_READ(sc, MII_BMCR);
                // 165                         PHY_WRITE(sc, MII_BMCR, reg | BMCR_ISO);
                // 166                         return (0);
                // 167                 }
                // 168
                // 169                 /*
                // 170                  * If the interface is not up, don't do anything.
                // 171                  */
                // 172                 if ((mii->mii_ifp->if_flags & IFF_UP) == 0)
                // 173                         break;
                // 174
                // 175                 mii_phy_setmedia(sc);
                // 176                 break;
                // 177
            }
            MiiOpCode::Tick => {
                // 178         case MII_TICK:
                // 179                 /*
                // 180                  * If we're not currently selected, just return.
                // 181                  */
                // 182                 if (IFM_INST(ife->ifm_media) != sc->mii_inst)
                // 183                         return (0);
                // 184
                // 185                 if (mii_phy_tick(sc) == EJUSTRETURN)
                // 186                         return (0);
                // 187                 break;
                // 188
            }
            MiiOpCode::Down => {
                // 189         case MII_DOWN:
                // 190                 mii_phy_down(sc);
                // 191                 return (0);
                // 192         }
                super::phy_down(ma);
                return;
            }
        }

        // 193
        // 194         /* Update the media status. */
        // 195         mii_phy_status(sc);

        // Update the media status.
        super::phy_status(parent, ma, self);

        // 196
        // 197         /* Callback if something changed. */
        // 198         mii_phy_update(sc, cmd);
        // 199         return (0);

        // Callback if something changed.

        todo!()
    }

    /// Media status subroutine.  If a PHY driver does media detection simply
    /// by decoding the NWay autonegotiation, use this routine.
    fn status(&self, parent: &mut dyn Mii, ma: &mut MiiAttachArgs) -> Result<(), MiiError> {
        {
            let mii = parent.get_data_mut();

            mii.media_status = IFM_AVALID;
            mii.media_active = IFM_ETHER;
        }

        let bmsr = parent
            .read_reg(ma.phy_no, MII_BMSR)
            .ok_or(MiiError::ReadError)?
            | parent
                .read_reg(ma.phy_no, MII_BMSR)
                .ok_or(MiiError::ReadError)?;

        if (bmsr & BMSR_LINK) != 0 {
            parent.get_data_mut().media_status |= IFM_ACTIVE;
        }

        let bmcr = parent
            .read_reg(ma.phy_no, MII_BMCR)
            .ok_or(MiiError::ReadError)?;
        if bmcr & BMCR_ISO != 0 {
            parent.get_data_mut().media_active |= IFM_NONE;
            parent.get_data_mut().media_status = 0;
            return Ok(());
        }

        if bmcr & BMCR_LOOP != 0 {
            parent.get_data_mut().media_active |= IFM_LOOP;
        }

        if bmcr & BMCR_AUTOEN != 0 {
            // NWay autonegotiation takes the highest-order common
            // bit of the ANAR and ANLPAR (i.e. best media advertised
            // both by us and our link partner).
            if bmsr & BMSR_ACOMP == 0 {
                // Erg, still trying, I guess...
                parent.get_data_mut().media_active |= IFM_NONE;
                return Ok(());
            }

            let anlpar = parent
                .read_reg(ma.phy_no, MII_ANAR)
                .ok_or(MiiError::ReadError)?
                & parent
                    .read_reg(ma.phy_no, MII_ANLPAR)
                    .ok_or(MiiError::ReadError)?;

            let gtcr;
            let gtsr;
            if ma.flags.contains(MiiFlags::HAVE_GTCR)
                && ma.ext_capabilities & (EXTSR_1000THDX | EXTSR_1000TFDX) != 0
            {
                gtcr = parent
                    .read_reg(ma.phy_no, MII_100T2CR)
                    .ok_or(MiiError::ReadError)?;
                gtsr = parent
                    .read_reg(ma.phy_no, MII_100T2SR)
                    .ok_or(MiiError::ReadError)?;
            } else {
                gtcr = 0;
                gtsr = 0;
            }

            let mii = parent.get_data_mut();

            if gtcr & GTCR_ADV_1000TFDX != 0 && gtsr & GTSR_LP_1000TFDX != 0 {
                mii.media_active |= IFM_1000_T | IFM_FDX;
            } else if gtcr & GTCR_ADV_1000THDX != 0 && gtsr & GTSR_LP_1000THDX != 0 {
                mii.media_active |= IFM_1000_T | IFM_HDX;
            } else if anlpar & ANLPAR_TX_FD != 0 {
                mii.media_active |= IFM_100_TX | IFM_FDX;
            } else if anlpar & ANLPAR_T4 != 0 {
                mii.media_active |= IFM_100_T4 | IFM_HDX;
            } else if anlpar & ANLPAR_TX != 0 {
                mii.media_active |= IFM_100_TX | IFM_HDX;
            } else if anlpar & ANLPAR_10_FD != 0 {
                mii.media_active |= IFM_10_T | IFM_FDX;
            } else if anlpar & ANLPAR_10 != 0 {
                mii.media_active |= IFM_10_T | IFM_HDX;
            } else {
                mii.media_active |= IFM_NONE;
            }

            if mii.media_active & IFM_FDX != 0 {
                parent.get_data_mut().media_active |= super::phy_flow_status(parent, ma)?;
            }

            let mii = parent.get_data_mut();

            if ifm_subtype(mii.media_active) == IFM_1000_T && (gtsr & GTSR_MS_RES != 0) {
                mii.media_active |= IFM_ETH_MASTER;
            }
        } else {
            parent.get_data_mut().media_active = ma.media_active;
        }

        Ok(())
    }

    fn reset(&self, parent: &mut dyn Mii) {}
}
