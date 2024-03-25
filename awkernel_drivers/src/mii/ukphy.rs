use super::*;

#[derive(Debug)]
pub struct Ukphy {
    ma: MiiAttachArgs,
}

impl Ukphy {
    pub fn new(ma: MiiAttachArgs) -> Self {
        Self { ma }
    }
}

impl MiiPhy for Ukphy {
    fn service(&mut self, parent: &mut dyn Mii, opcode: MiiOpCode) -> Result<(), MiiError> {
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

                // If we're not polling our PHY instance, just return.
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

                // If the media indicates a different PHY instance,
                // isolate ourselves.

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

                // If we're not currently selected, just return.

                // 184
                // 185                 if (mii_phy_tick(sc) == EJUSTRETURN)
                // 186                         return (0);
                // 187                 break;
                // 188

                if phy_tick(parent, self)? == JustReturn::Yes {
                    return Ok(());
                }
            }
            MiiOpCode::Down => {
                // 189         case MII_DOWN:
                // 190                 mii_phy_down(sc);
                // 191                 return (0);
                // 192         }
                super::phy_down(&mut self.ma);
                return Ok(());
            }
        }

        // 193
        // 194         /* Update the media status. */
        // 195         mii_phy_status(sc);

        // Update the media status.
        self.status(parent)?;

        // 196
        // 197         /* Callback if something changed. */
        // 198         mii_phy_update(sc, cmd);
        // 199         return (0);

        // Callback if something changed.
        super::phy_update(parent, &mut self.ma, opcode)?;

        Ok(())
    }

    /// Media status subroutine.  If a PHY driver does media detection simply
    /// by decoding the NWay autonegotiation, use this routine.
    fn status(&mut self, parent: &mut dyn Mii) -> Result<(), MiiError> {
        let ma = self.get_attach_args();

        {
            let mii = parent.get_data_mut();

            mii.media_status = Media::new(IFM_AVALID);
            mii.media_active = Media::new(IFM_ETHER);
        }

        let bmsr = BMSR::from_bits_retain(
            parent.read_reg(ma.phy_no, MII_BMSR)? | parent.read_reg(ma.phy_no, MII_BMSR)?,
        );

        if bmsr.contains(BMSR::LINK) {
            parent.get_data_mut().media_status.insert(IFM_ACTIVE);
        }

        let bmcr = parent.read_reg(ma.phy_no, MII_BMCR)?;
        if bmcr & BMCR_ISO != 0 {
            parent.get_data_mut().media_active.insert(IFM_NONE);
            parent.get_data_mut().media_status = Media::new(0);
            return Ok(());
        }

        if bmcr & BMCR_LOOP != 0 {
            parent.get_data_mut().media_active.insert(IFM_LOOP);
        }

        if bmcr & BMCR_AUTOEN != 0 {
            // NWay autonegotiation takes the highest-order common
            // bit of the ANAR and ANLPAR (i.e. best media advertised
            // both by us and our link partner).
            if !bmsr.contains(BMSR::ACOMP) {
                // Erg, still trying, I guess...
                parent.get_data_mut().media_active.insert(IFM_NONE);
                return Ok(());
            }

            let anlpar =
                parent.read_reg(ma.phy_no, MII_ANAR)? & parent.read_reg(ma.phy_no, MII_ANLPAR)?;

            let gtcr;
            let gtsr;
            if ma.flags.contains(MiiFlags::HAVE_GTCR)
                && ma
                    .ext_capabilities
                    .intersects(EXTSR::ETH_1000THDX | EXTSR::ETH_1000TFDX)
            {
                gtcr = parent.read_reg(ma.phy_no, MII_100T2CR)?;
                gtsr = parent.read_reg(ma.phy_no, MII_100T2SR)?;
            } else {
                gtcr = 0;
                gtsr = 0;
            }

            let mii = parent.get_data_mut();

            if gtcr & GTCR_ADV_1000TFDX != 0 && gtsr & GTSR_LP_1000TFDX != 0 {
                mii.media_active.insert(IFM_1000_T | IFM_FDX);
            } else if gtcr & GTCR_ADV_1000THDX != 0 && gtsr & GTSR_LP_1000THDX != 0 {
                mii.media_active.insert(IFM_1000_T | IFM_HDX);
            } else if anlpar & ANLPAR_TX_FD != 0 {
                mii.media_active.insert(IFM_100_TX | IFM_FDX);
            } else if anlpar & ANLPAR_T4 != 0 {
                mii.media_active.insert(IFM_100_T4 | IFM_HDX);
            } else if anlpar & ANLPAR_TX != 0 {
                mii.media_active.insert(IFM_100_TX | IFM_HDX);
            } else if anlpar & ANLPAR_10_FD != 0 {
                mii.media_active.insert(IFM_10_T | IFM_FDX);
            } else if anlpar & ANLPAR_10 != 0 {
                mii.media_active.insert(IFM_10_T | IFM_HDX);
            } else {
                mii.media_active.insert(IFM_NONE);
            }

            if mii.media_active.contains(IFM_FDX) {
                let flags = super::phy_flow_status(parent, &mut self.ma)?;
                parent.get_data_mut().media_active.insert(flags);
            }

            let mii = parent.get_data_mut();

            if ifm_subtype(&mii.media_active) == IFM_1000_T && (gtsr & GTSR_MS_RES != 0) {
                mii.media_active.insert(IFM_ETH_MASTER);
            }
        } else {
            parent.get_data_mut().media_active = ma.media_active;
        }

        Ok(())
    }

    fn attach(&mut self, parent: &mut dyn Mii) -> Result<(), MiiError> {
        log::info!(
            "Generic IEEE 802.3u media interface has been found. rev {}, OUI 0x{:06x} model 0x{:04x}",
            mii_rev(self.ma.id2),
            mii_oui(self.ma.id1, self.ma.id2),
            mii_model(self.ma.id2)
        );

        self.ma.instance = parent.get_data().instance;

        self.ma.flags.insert(MiiFlags::NOLOOP);

        self.reset(parent)?;

        self.ma.capabilities =
            BMSR::from_bits_retain(parent.read_reg(self.ma.phy_no, MII_BMSR)? & self.ma.capmask);

        if self.ma.capabilities.contains(BMSR::EXTSTAT) {
            self.ma.ext_capabilities =
                EXTSR::from_bits_retain(parent.read_reg(self.ma.phy_no, MII_EXTSR)?);
        }

        if !self.ma.capabilities.intersects(bmsr_media_mask())
            && !self.ma.ext_capabilities.intersects(extsr_media_mask())
        {
            log::warn!("No media present");
        } else {
            super::phy_add_media(parent, &mut self.ma);
        }

        Ok(())
    }

    fn get_attach_args(&self) -> &MiiAttachArgs {
        &self.ma
    }

    fn get_attach_args_mut(&mut self) -> &mut MiiAttachArgs {
        &mut self.ma
    }
}
