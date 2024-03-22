use crate::{
    if_media::{
        IFM_1000_T, IFM_100_T4, IFM_100_TX, IFM_10_T, IFM_ACTIVE, IFM_AVALID, IFM_ETHER, IFM_FDX,
        IFM_HDX, IFM_LOOP, IFM_NONE,
    },
    mii::{BMSR_LINK, MII_BMCR, MII_BMSR},
};

use super::{
    Mii, MiiAttachArgs, MiiError, MiiFlags, MiiOpCode, MiiPhy, ANLPAR_10, ANLPAR_10_FD, ANLPAR_T4,
    ANLPAR_TX, ANLPAR_TX_FD, BMCR_AUTOEN, BMCR_ISO, BMCR_LOOP, BMSR_ACOMP, EXTSR_1000TFDX,
    EXTSR_1000THDX, GTCR_ADV_1000TFDX, GTCR_ADV_1000THDX, GTSR_LP_1000TFDX, GTSR_LP_1000THDX,
    MII_100T2CR, MII_100T2SR, MII_ANAR, MII_ANLPAR,
};

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
        // 54 void
        // 55 ukphy_status(struct mii_softc *phy)
        //    /* [previous][next][first][last][top][bottom][index][help]  */
        // 56 {
        // 57         struct mii_data *mii = phy->mii_pdata;
        // 58         struct ifmedia_entry *ife = mii->mii_media.ifm_cur;
        // 59         int bmsr, bmcr, anlpar, gtcr, gtsr;

        {
            let mii = parent.get_data_mut();

            // 60
            // 61         mii->mii_media_status = IFM_AVALID;
            // 62         mii->mii_media_active = IFM_ETHER;

            mii.media_status = IFM_AVALID;
            mii.media_active = IFM_ETHER;
        }

        // 63
        // 64         bmsr = PHY_READ(phy, MII_BMSR) | PHY_READ(phy, MII_BMSR);
        // 65         if (bmsr & BMSR_LINK)
        // 66                 mii->mii_media_status |= IFM_ACTIVE;

        let bmsr = parent
            .read_reg(ma.phy_no, MII_BMSR)
            .ok_or(MiiError::ReadError)?
            | parent
                .read_reg(ma.phy_no, MII_BMSR)
                .ok_or(MiiError::ReadError)?;

        if (bmsr & BMSR_LINK) != 0 {
            parent.get_data_mut().media_status |= IFM_ACTIVE;
        }

        // 67
        // 68         bmcr = PHY_READ(phy, MII_BMCR);
        // 69         if (bmcr & BMCR_ISO) {
        // 70                 mii->mii_media_active |= IFM_NONE;
        // 71                 mii->mii_media_status = 0;
        // 72                 return;
        // 73         }

        let bmcr = parent
            .read_reg(ma.phy_no, MII_BMCR)
            .ok_or(MiiError::ReadError)?;
        if bmcr & BMCR_ISO != 0 {
            parent.get_data_mut().media_active |= IFM_NONE;
            parent.get_data_mut().media_status = 0;
            return Ok(());
        }

        // 74
        // 75         if (bmcr & BMCR_LOOP)
        // 76                 mii->mii_media_active |= IFM_LOOP;

        if bmcr & BMCR_LOOP != 0 {
            parent.get_data_mut().media_active |= IFM_LOOP;
        }

        if bmcr & BMCR_AUTOEN != 0 {
            // 77
            // 78         if (bmcr & BMCR_AUTOEN) {
            // 79                 /*
            // 80                  * NWay autonegotiation takes the highest-order common
            // 81                  * bit of the ANAR and ANLPAR (i.e. best media advertised
            // 82                  * both by us and our link partner).
            // 83                  */
            // 84                 if ((bmsr & BMSR_ACOMP) == 0) {
            // 85                         /* Erg, still trying, I guess... */
            // 86                         mii->mii_media_active |= IFM_NONE;
            // 87                         return;
            // 88                 }

            // NWay autonegotiation takes the highest-order common
            // bit of the ANAR and ANLPAR (i.e. best media advertised
            // both by us and our link partner).
            if bmsr & BMSR_ACOMP == 0 {
                // Erg, still trying, I guess...
                parent.get_data_mut().media_active |= IFM_NONE;
                return Ok(());
            }

            // 89
            // 90                 anlpar = PHY_READ(phy, MII_ANAR) & PHY_READ(phy, MII_ANLPAR);

            let anlpar = parent
                .read_reg(ma.phy_no, MII_ANAR)
                .ok_or(MiiError::ReadError)?
                & parent
                    .read_reg(ma.phy_no, MII_ANLPAR)
                    .ok_or(MiiError::ReadError)?;

            // 91                 if ((phy->mii_flags & MIIF_HAVE_GTCR) != 0 &&
            // 92                     (phy->mii_extcapabilities &
            // 93                      (EXTSR_1000THDX|EXTSR_1000TFDX)) != 0) {
            // 94                         gtcr = PHY_READ(phy, MII_100T2CR);
            // 95                         gtsr = PHY_READ(phy, MII_100T2SR);
            // 96                 } else
            // 97                         gtcr = gtsr = 0;

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

            // 98
            // 99                 if ((gtcr & GTCR_ADV_1000TFDX) && (gtsr & GTSR_LP_1000TFDX))
            // 100                         mii->mii_media_active |= IFM_1000_T|IFM_FDX;

            let mii = parent.get_data_mut();

            if gtcr & GTCR_ADV_1000TFDX != 0 && gtsr & GTSR_LP_1000TFDX != 0 {
                mii.media_active |= IFM_1000_T | IFM_FDX;
            }
            // 101                 else if ((gtcr & GTCR_ADV_1000THDX) &&
            // 102                          (gtsr & GTSR_LP_1000THDX))
            // 103                         mii->mii_media_active |= IFM_1000_T|IFM_HDX;
            else if gtcr & GTCR_ADV_1000THDX != 0 && gtsr & GTSR_LP_1000THDX != 0 {
                mii.media_active |= IFM_1000_T | IFM_HDX;
            // 104                 else if (anlpar & ANLPAR_TX_FD)
            // 105                         mii->mii_media_active |= IFM_100_TX|IFM_FDX;
            } else if anlpar & ANLPAR_TX_FD != 0 {
                mii.media_active |= IFM_100_TX | IFM_FDX;
            // 106                 else if (anlpar & ANLPAR_T4)
            // 107                         mii->mii_media_active |= IFM_100_T4|IFM_HDX;
            } else if anlpar & ANLPAR_T4 != 0 {
                mii.media_active |= IFM_100_T4 | IFM_HDX;
            }
            // 108                 else if (anlpar & ANLPAR_TX)
            // 109                         mii->mii_media_active |= IFM_100_TX|IFM_HDX;
            else if anlpar & ANLPAR_TX != 0 {
                mii.media_active |= IFM_100_TX | IFM_HDX;
            // 110                 else if (anlpar & ANLPAR_10_FD)
            // 111                         mii->mii_media_active |= IFM_10_T|IFM_FDX;
            } else if anlpar & ANLPAR_10_FD != 0 {
                mii.media_active |= IFM_10_T | IFM_FDX;
            }
            // 112                 else if (anlpar & ANLPAR_10)
            // 113                         mii->mii_media_active |= IFM_10_T|IFM_HDX;
            else if anlpar & ANLPAR_10 != 0 {
                mii.media_active |= IFM_10_T | IFM_HDX;
            }
            // 114                 else
            // 115                         mii->mii_media_active |= IFM_NONE;
            else {
                mii.media_active |= IFM_NONE;
            }

            // 116
            // 117                 if (mii->mii_media_active & IFM_FDX)
            // 118                         mii->mii_media_active |= mii_phy_flowstatus(phy);

            if mii.media_active & IFM_FDX != 0 {
                // TODO
                // mii->mii_media_active |= mii_phy_flowstatus(phy);
            }

            // 119
            // 120                 if ((IFM_SUBTYPE(mii->mii_media_active) == IFM_1000_T) &&
            // 121                     (gtsr & GTSR_MS_RES))
            // 122                         mii->mii_media_active |= IFM_ETH_MASTER;
        } else {
            parent.get_data_mut().media_active = ma.media_active;
        }

        Ok(())
    }

    fn reset(&self, parent: &mut dyn Mii) {}
}
