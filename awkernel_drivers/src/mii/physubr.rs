use crate::if_media::{
    ifm_make_word, ifm_subtype, IfmediaEntry, IFM_1000_SX, IFM_1000_T, IFM_100_FX, IFM_100_T4,
    IFM_100_TX, IFM_10_T, IFM_ETH_MASTER, IFM_ETH_RXPAUSE, IFM_ETH_TXPAUSE, IFM_FDX, IFM_FLOW,
    IFM_HPNA_1, IFM_NONE,
};

use super::*;

pub fn phy_dev_attach(
    mii: &mut dyn Mii,
    mii_data: &mut MiiData,
    flags: MiiFlags,
    phy: &mut dyn MiiPhy,
) -> Result<(), MiiError> {
    let phy_data = phy.get_phy_data_mut();

    phy_data.flags |= flags;

    phy.reset(mii, mii_data)?;

    let phy_data = phy.get_phy_data_mut();

    phy_data.capabilities = mii.read_reg(phy_data.phy, MII_BMSR)? & phy_data.capmask;
    if phy_data.capabilities & BMSR_EXTSTAT != 0 {
        phy_data.extcapabilities = mii.read_reg(phy_data.phy, MII_EXTSR)?;
    }

    if phy_data.maxspeed == 100 {
        // This is a bit tricky.
        // If we have a 1G capable PHY, but we don't want to advertise
        // 1G capabilities we need to clear the GTCR register before
        // doing autonegotiation.
        // Clearing the register here is not enough since its value
        // can be restored after PHY_RESET is called.
        if phy_data.extcapabilities & (EXTSR_1000THDX | EXTSR_1000TFDX) != 0 {
            phy_data.flags |= MiiFlags::HAVE_GTCR;
        }

        phy_data.extcapabilities = 0;
    }

    phy_add_media(mii_data, phy);
    mii.media_init(mii_data)?;

    let phy_data = phy.get_phy_data_mut();

    // If maxspeed was specified we have to restart autonegotiation.
    // PHY might have attempted it and failed due to having mistakenly
    // advertising modes that we do not in fact support.
    if phy_data.maxspeed != 0 {
        phy_data.flags |= MiiFlags::FORCEANEG;
        phy_set_media(mii, mii_data, phy)?;

        let phy_data = phy.get_phy_data_mut();
        phy_data.flags &= !MiiFlags::FORCEANEG;
    }

    // log::debug!("mii_data = {:?}", mii_data);

    Ok(())
}

pub fn phy_reset(
    mii: &mut dyn Mii,
    mii_data: &MiiData,
    phy: &mut dyn MiiPhy,
) -> Result<(), MiiError> {
    let phy_data = phy.get_phy_data();

    let mut reg = if phy_data.flags.contains(MiiFlags::NOISOLATE) {
        BMCR_RESET
    } else {
        BMCR_RESET | BMCR_ISO
    };

    mii.write_reg(phy_data.phy, MII_BMCR, reg)?;

    // Wait 100ms for it to complete.
    for _ in 0..100 {
        reg = mii.read_reg(phy_data.phy, MII_BMCR)?;

        if (reg & BMCR_RESET) == 0 {
            break;
        }
        awkernel_lib::delay::wait_microsec(1000);
    }

    // NB: a PHY may default to being powered down and/or isolated.
    reg &= !(BMCR_PDOWN | BMCR_ISO);

    if !phy_data.flags.contains(MiiFlags::NOISOLATE) {
        if let Some(ife) = mii_data.media.get_current() {
            if ife.get_instance() != phy_data.inst {
                reg |= BMCR_ISO;
            }
        } else if phy_data.inst != 0 {
            reg |= BMCR_ISO;
        }
    }

    if mii.read_reg(phy_data.phy, MII_BMCR)? != reg {
        mii.write_reg(phy_data.phy, MII_BMCR, reg)?;
    }

    Ok(())
}

fn phy_add_media(mii_data: &mut MiiData, phy: &mut dyn MiiPhy) {
    let mut fdx = false;

    let phy_data = phy.get_phy_data_mut();

    if phy_data.capabilities & BMSR_MEDIAMASK == 0
        && phy_data.extcapabilities & EXTSR_MEDIAMASK == 0
    {
        // no media present
        return;
    }

    // Set the autonegotiation timer for 10/100 media.  Gigabit media is
    // handled below.
    phy_data.anegticks = MII_ANEGTICKS;

    if !phy_data.flags.contains(MiiFlags::NOISOLATE) {
        mii_data.media.add(IfmediaEntry {
            media: ifm_make_word(IFM_ETHER, IFM_NONE, 0, phy_data.inst as u64),
            data: 0,
        });
    }

    // There are different interpretations for the bits in
    // HomePNA PHYs.  And there is really only one media type
    // that is supported.
    if phy_data.flags.contains(MiiFlags::IS_HPNA) {
        if phy_data.capabilities & BMSR_10THDX != 0 {
            mii_data.media.add(IfmediaEntry {
                media: ifm_make_word(IFM_ETHER, IFM_HPNA_1, 0, phy_data.inst as u64),
                data: 0,
            });
        }

        return;
    }

    if phy_data.capabilities & BMSR_10THDX != 0 {
        mii_data.media.add(IfmediaEntry {
            media: ifm_make_word(IFM_ETHER, IFM_10_T, 0, phy_data.inst as u64),
            data: 0,
        });
    }

    if phy_data.capabilities & BMSR_10TFDX != 0 {
        mii_data.media.add(IfmediaEntry {
            media: ifm_make_word(IFM_ETHER, IFM_10_T, IFM_FDX, phy_data.inst as u64),
            data: 0,
        });

        if phy_data.flags.contains(MiiFlags::DOPAUSE)
            && !phy_data.flags.contains(MiiFlags::NOMANPAUSE)
        {
            mii_data.media.add(IfmediaEntry {
                media: ifm_make_word(
                    IFM_ETHER,
                    IFM_10_T,
                    IFM_FDX | IFM_FLOW,
                    phy_data.inst as u64,
                ),
                data: 0,
            });
        }

        fdx = true;
    }

    if phy_data.capabilities & BMSR_100TXHDX != 0 {
        mii_data.media.add(IfmediaEntry {
            media: ifm_make_word(IFM_ETHER, IFM_100_TX, 0, phy_data.inst as u64),
            data: 0,
        });
    }

    if phy_data.capabilities & BMSR_100TXFDX != 0 {
        mii_data.media.add(IfmediaEntry {
            media: ifm_make_word(IFM_ETHER, IFM_100_TX, IFM_FDX, phy_data.inst as u64),
            data: 0,
        });

        if phy_data.flags.contains(MiiFlags::DOPAUSE)
            && !phy_data.flags.contains(MiiFlags::NOMANPAUSE)
        {
            mii_data.media.add(IfmediaEntry {
                media: ifm_make_word(
                    IFM_ETHER,
                    IFM_100_TX,
                    IFM_FDX | IFM_FLOW,
                    phy_data.inst as u64,
                ),
                data: 0,
            });
        }

        fdx = true;
    }

    if phy_data.capabilities & BMSR_100T4 != 0 {
        mii_data.media.add(IfmediaEntry {
            media: ifm_make_word(IFM_ETHER, IFM_100_T4, 0, phy_data.inst as u64),
            data: 0,
        });
    }

    if phy_data.extcapabilities & EXTSR_MEDIAMASK != 0 {
        // XXX Right now only handle 1000SX and 1000TX.  Need
        // XXX to handle 1000LX and 1000CX somehow.
        if phy_data.extcapabilities & EXTSR_1000XHDX != 0 {
            phy_data.anegticks = MII_ANEGTICKS_GIGE;
            phy_data.flags |= MiiFlags::IS_1000X;

            mii_data.media.add(IfmediaEntry {
                media: ifm_make_word(IFM_ETHER, IFM_1000_SX, 0, phy_data.inst as u64),
                data: 0,
            });
        }

        if phy_data.extcapabilities & EXTSR_1000XFDX != 0 {
            phy_data.anegticks = MII_ANEGTICKS_GIGE;
            phy_data.flags |= MiiFlags::IS_1000X;

            mii_data.media.add(IfmediaEntry {
                media: ifm_make_word(IFM_ETHER, IFM_1000_SX, IFM_FDX, phy_data.inst as u64),
                data: 0,
            });

            if phy_data.flags.contains(MiiFlags::DOPAUSE)
                && !phy_data.flags.contains(MiiFlags::NOMANPAUSE)
            {
                mii_data.media.add(IfmediaEntry {
                    media: ifm_make_word(
                        IFM_ETHER,
                        IFM_1000_SX,
                        IFM_FDX | IFM_FLOW,
                        phy_data.inst as u64,
                    ),
                    data: 0,
                });
            }

            fdx = true;
        }

        // 1000baseT media needs to be able to manipulate
        // master/slave mode.
        //
        // All 1000baseT PHYs have a 1000baseT control register.
        if phy_data.extcapabilities & EXTSR_1000THDX != 0 {
            phy_data.anegticks = MII_ANEGTICKS_GIGE;
            phy_data.flags |= MiiFlags::HAVE_GTCR;

            mii_data.media.add(IfmediaEntry {
                media: ifm_make_word(IFM_ETHER, IFM_1000_T, 0, phy_data.inst as u64),
                data: 0,
            });

            mii_data.media.add(IfmediaEntry {
                media: ifm_make_word(IFM_ETHER, IFM_1000_T, IFM_ETH_MASTER, phy_data.inst as u64),
                data: 0,
            });
        }

        if phy_data.extcapabilities & EXTSR_1000TFDX != 0 {
            phy_data.anegticks = MII_ANEGTICKS_GIGE;
            phy_data.flags |= MiiFlags::HAVE_GTCR;

            mii_data.media.add(IfmediaEntry {
                media: ifm_make_word(IFM_ETHER, IFM_1000_T, IFM_FDX, phy_data.inst as u64),
                data: 0,
            });

            mii_data.media.add(IfmediaEntry {
                media: ifm_make_word(
                    IFM_ETHER,
                    IFM_1000_T,
                    IFM_FDX | IFM_ETH_MASTER,
                    phy_data.inst as u64,
                ),
                data: 0,
            });

            if phy_data.flags.contains(MiiFlags::DOPAUSE)
                && !phy_data.flags.contains(MiiFlags::NOMANPAUSE)
            {
                mii_data.media.add(IfmediaEntry {
                    media: ifm_make_word(
                        IFM_ETHER,
                        IFM_1000_T,
                        IFM_FDX | IFM_FLOW,
                        phy_data.inst as u64,
                    ),
                    data: 0,
                });

                mii_data.media.add(IfmediaEntry {
                    media: ifm_make_word(
                        IFM_ETHER,
                        IFM_1000_T,
                        IFM_FDX | IFM_FLOW | IFM_ETH_MASTER,
                        phy_data.inst as u64,
                    ),
                    data: 0,
                });
            }

            fdx = true;
        }
    }

    if phy_data.extcapabilities & EXTSR_MEDIAMASK != 0 {
        if phy_data.extcapabilities & EXTSR_1000XHDX != 0 {
            phy_data.anegticks = MII_ANEGTICKS_GIGE;
            phy_data.flags |= MiiFlags::IS_1000X;

            mii_data.media.add(IfmediaEntry {
                media: ifm_make_word(IFM_ETHER, IFM_1000_SX, 0, phy_data.inst as u64),
                data: 0,
            });

            if phy_data.extcapabilities & EXTSR_1000XFDX != 0 {
                mii_data.media.add(IfmediaEntry {
                    media: ifm_make_word(IFM_ETHER, IFM_1000_SX, IFM_FDX, phy_data.inst as u64),
                    data: 0,
                });

                if phy_data.flags.contains(MiiFlags::DOPAUSE)
                    && !phy_data.flags.contains(MiiFlags::NOMANPAUSE)
                {
                    mii_data.media.add(IfmediaEntry {
                        media: ifm_make_word(
                            IFM_ETHER,
                            IFM_1000_SX,
                            IFM_FDX | IFM_FLOW,
                            phy_data.inst as u64,
                        ),
                        data: 0,
                    });
                }

                fdx = true;
            }
        }
    }

    if phy_data.capabilities & BMSR_ANEG != 0 {
        mii_data.media.add(IfmediaEntry {
            media: ifm_make_word(IFM_ETHER, IFM_AUTO, 0, phy_data.inst as u64),
            data: 0,
        });

        if fdx && phy_data.flags.contains(MiiFlags::DOPAUSE) {
            mii_data.media.add(IfmediaEntry {
                media: ifm_make_word(IFM_ETHER, IFM_AUTO, IFM_FLOW, phy_data.inst as u64),
                data: 0,
            });
        }
    }
}

pub fn phy_set_media(
    mii: &mut dyn Mii,
    mii_data: &MiiData,
    phy: &mut dyn MiiPhy,
) -> Result<(), MiiError> {
    let phy_data = phy.get_phy_data();

    // 123         struct mii_data *mii = sc->mii_pdata;
    // 124         struct ifmedia_entry *ife = mii->mii_media.ifm_cur;
    // 125         int bmcr, anar, gtcr;
    // 126         int index = -1;

    let Some(ife) = mii_data.media.get_current() else {
        return Err(MiiError::Media);
    };

    log::debug!("ife = {:?}", ife);

    // 127
    // 128         switch (IFM_SUBTYPE(ife->ifm_media)) {
    // 129         case IFM_AUTO:
    // 130                 /*
    // 131                  * Force renegotiation if MIIF_DOPAUSE or MIIF_FORCEANEG.
    // 132                  * The former is necessary as we might switch from flow-
    // 133                  * control advertisement being off to on or vice versa.
    // 134                  */
    // 135                 if ((PHY_READ(sc, MII_BMCR) & BMCR_AUTOEN) == 0 ||
    // 136                     (sc->mii_flags & (MIIF_DOPAUSE | MIIF_FORCEANEG)) != 0)
    // 137                         (void)mii_phy_auto(sc);
    // 138                 return;
    // 139
    // 140         case IFM_NONE:
    // 141                 index = MII_MEDIA_NONE;
    // 142                 break;
    // 143
    // 144         case IFM_HPNA_1:
    // 145                 index = MII_MEDIA_10_T;
    // 146                 break;
    // 147
    // 148         case IFM_10_T:
    // 149                 switch (IFM_OPTIONS(ife->ifm_media)) {
    // 150                 case 0:
    // 151                         index = MII_MEDIA_10_T;
    // 152                         break;
    // 153                 case IFM_FDX:
    // 154                 case (IFM_FDX | IFM_FLOW):
    // 155                         index = MII_MEDIA_10_T_FDX;
    // 156                         break;
    // 157                 }
    // 158                 break;
    // 159
    // 160         case IFM_100_TX:
    // 161         case IFM_100_FX:
    // 162                 switch (IFM_OPTIONS(ife->ifm_media)) {
    // 163                 case 0:
    // 164                         index = MII_MEDIA_100_TX;
    // 165                         break;
    // 166                 case IFM_FDX:
    // 167                 case (IFM_FDX | IFM_FLOW):
    // 168                         index = MII_MEDIA_100_TX_FDX;
    // 169                         break;
    // 170                 }
    // 171                 break;
    // 172
    // 173         case IFM_100_T4:
    // 174                 index = MII_MEDIA_100_T4;
    // 175                 break;
    // 176
    // 177         case IFM_1000_SX:
    // 178                 switch (IFM_OPTIONS(ife->ifm_media)) {
    // 179                 case 0:
    // 180                         index = MII_MEDIA_1000_X;
    // 181                         break;
    // 182                 case IFM_FDX:
    // 183                 case (IFM_FDX | IFM_FLOW):
    // 184                         index = MII_MEDIA_1000_X_FDX;
    // 185                         break;
    // 186                 }
    // 187                 break;
    // 188
    // 189         case IFM_1000_T:
    // 190                 switch (IFM_OPTIONS(ife->ifm_media)) {
    // 191                 case 0:
    // 192                 case IFM_ETH_MASTER:
    // 193                         index = MII_MEDIA_1000_T;
    // 194                         break;
    // 195                 case IFM_FDX:
    // 196                 case (IFM_FDX | IFM_ETH_MASTER):
    // 197                 case (IFM_FDX | IFM_FLOW):
    // 198                 case (IFM_FDX | IFM_FLOW | IFM_ETH_MASTER):
    // 199                         index = MII_MEDIA_1000_T_FDX;
    // 200                         break;
    // 201                 }
    // 202                 break;
    // 203         }

    match ifm_subtype(&ife.media) {
        IFM_AUTO => {
            // Force renegotiation if MIIF_DOPAUSE or MIIF_FORCEANEG.
            // The former is necessary as we might switch from flow-
            // control advertisement being off to on or vice versa.
            // 134                  */
            // 135                 if ((PHY_READ(sc, MII_BMCR) & BMCR_AUTOEN) == 0 ||
            // 136                     (sc->mii_flags & (MIIF_DOPAUSE | MIIF_FORCEANEG)) != 0)
            // 137                         (void)mii_phy_auto(sc);

            log::debug!("IFM_AUTO");

            if mii.read_reg(phy_data.phy, MII_BMCR)? & BMCR_AUTOEN == 0
                || phy_data
                    .flags
                    .intersects(MiiFlags::DOPAUSE | MiiFlags::FORCEANEG)
            {
                log::debug!("mii_phy_auto");
            }

            return Ok(());
        }
        IFM_NONE => {}
        IFM_HPNA_1 => {}
        IFM_10_T => {}
        IFM_100_TX | IFM_100_FX => {}
        IFM_100_T4 => {}
        IFM_1000_SX => {}
        IFM_1000_T => {}
        _ => {
            return Err(MiiError::Media);
        }
    }

    // 204
    // 205         KASSERT(index != -1, ("%s: failed to map media word %d",
    // 206             __func__, ife->ifm_media));
    // 207
    // 208         anar = mii_media_table[index].mm_anar;
    // 209         bmcr = mii_media_table[index].mm_bmcr;
    // 210         gtcr = mii_media_table[index].mm_gtcr;
    // 211
    // 212         if (IFM_SUBTYPE(ife->ifm_media) == IFM_1000_T) {
    // 213                 gtcr |= GTCR_MAN_MS;
    // 214                 if ((ife->ifm_media & IFM_ETH_MASTER) != 0)
    // 215                         gtcr |= GTCR_ADV_MS;
    // 216         }
    // 217
    // 218         if ((ife->ifm_media & IFM_FDX) != 0 &&
    // 219             ((ife->ifm_media & IFM_FLOW) != 0 ||
    // 220             (sc->mii_flags & MIIF_FORCEPAUSE) != 0)) {
    // 221                 if ((sc->mii_flags & MIIF_IS_1000X) != 0)
    // 222                         anar |= ANAR_X_PAUSE_TOWARDS;
    // 223                 else {
    // 224                         anar |= ANAR_FC;
    // 225                         /* XXX Only 1000BASE-T has PAUSE_ASYM? */
    // 226                         if ((sc->mii_flags & MIIF_HAVE_GTCR) != 0 &&
    // 227                             (sc->mii_extcapabilities &
    // 228                             (EXTSR_1000THDX | EXTSR_1000TFDX)) != 0)
    // 229                                 anar |= ANAR_X_PAUSE_ASYM;
    // 230                 }
    // 231         }
    // 232
    // 233         PHY_WRITE(sc, MII_ANAR, anar);
    // 234         PHY_WRITE(sc, MII_BMCR, bmcr);
    // 235         if ((sc->mii_flags & MIIF_HAVE_GTCR) != 0)
    // 236                 PHY_WRITE(sc, MII_100T2CR, gtcr);

    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TickReturn {
    JustReturn,
    Continue,
}

pub fn phy_tick(
    mii: &mut dyn Mii,
    mii_data: &mut MiiData,
    phy: &mut dyn MiiPhy,
) -> Result<TickReturn, MiiError> {
    log::debug!("phy_tick");

    let Some(ife) = mii_data.media.get_current() else {
        return Err(MiiError::Media);
    };

    let phy_data = phy.get_phy_data_mut();

    // If we're not doing autonegotiation, we don't need to do
    // any extra work here.  However, we need to check the link
    // status so we can generate an announcement if the status
    // changes.
    if ifm_subtype(&ife.media) != IFM_AUTO {
        phy_data.ticks = 0; // reset autonegotiation timer.
        log::debug!("not doing autonegotiation");
        return Ok(TickReturn::Continue);
    }

    // Read the status register twice; BMSR_LINK is latch-low.
    let reg = mii.read_reg(phy_data.phy, MII_BMSR)? | mii.read_reg(phy_data.phy, MII_BMSR)?;
    if reg & BMSR_LINK != 0 {
        log::debug!("link up");
        phy_data.ticks = 0; // reset autonegotiation timer.
        return Ok(TickReturn::Continue);
    }

    // Announce link loss right after it happens
    let tick = phy_data.ticks;
    phy_data.ticks += 1;
    if tick == 0 {
        return Ok(TickReturn::Continue);
    }

    // XXX: use default value if phy driver did not set mii_anegticks
    if phy_data.anegticks == 0 {
        phy_data.anegticks = MII_ANEGTICKS_GIGE;
    }

    // Only retry autonegotiation every mii_anegticks ticks.
    if phy_data.ticks <= phy_data.anegticks {
        return Ok(TickReturn::JustReturn);
    }

    phy_data.ticks = 0;
    phy.reset(mii, mii_data)?;
    phy_auto(mii, mii_data, phy)?;

    Ok(TickReturn::Continue)
}

fn phy_auto(mii: &mut dyn Mii, mii_data: &MiiData, phy: &mut dyn MiiPhy) -> Result<(), MiiError> {
    // TODO

    log::debug!("phy_auto");

    Ok(())
}

/// Return the flow control status flag from MII_ANAR & MII_ANLPAR.
pub fn phy_flowstatus(mii: &mut dyn Mii, phy: &dyn MiiPhy) -> Result<u64, MiiError> {
    let phy_data = phy.get_phy_data();

    if !phy_data.flags.contains(MiiFlags::DOPAUSE) {
        return Ok(0);
    }

    let mut anar = mii.read_reg(phy_data.phy, MII_ANAR)?;
    let mut anlpar = mii.read_reg(phy_data.phy, MII_ANLPAR)?;

    // Check for 1000BASE-X.  Autonegotiation is a bit
    // different on such devices.
    if phy_data.flags.contains(MiiFlags::IS_1000X) {
        anar <<= 3;
        anlpar <<= 3;
    }

    if anar & ANLPAR_PAUSE_SYM != 0 && anlpar & ANLPAR_PAUSE_SYM != 0 {
        return Ok(IFM_FLOW | IFM_ETH_TXPAUSE | IFM_ETH_RXPAUSE);
    }

    if anar & ANAR_PAUSE_SYM == 0 {
        if anar & ANAR_PAUSE_ASYM != 0 && anlpar & ANLPAR_PAUSE_TOWARDS != 0 {
            return Ok(IFM_FLOW | IFM_ETH_TXPAUSE);
        } else {
            return Ok(0);
        }
    }

    if anar & ANAR_PAUSE_ASYM == 0 {
        if anlpar & ANLPAR_PAUSE_SYM != 0 {
            return Ok(IFM_FLOW | IFM_ETH_TXPAUSE | IFM_ETH_RXPAUSE);
        } else {
            return Ok(0);
        }
    }

    match anlpar & ANLPAR_PAUSE_TOWARDS {
        ANLPAR_PAUSE_NONE => Ok(0),
        ANLPAR_PAUSE_ASYM => Ok(IFM_FLOW | IFM_ETH_RXPAUSE),
        _ => Ok(IFM_FLOW | IFM_ETH_RXPAUSE | IFM_ETH_TXPAUSE),
    }
}

pub fn phy_update(
    mii: &mut dyn Mii,
    mii_data: &mut MiiData,
    phy: &mut dyn MiiPhy,
    cmd: MiiPhyCmd,
) -> Result<(), MiiError> {
    let phy_data = phy.get_phy_data_mut();

    if mii_data.media_active != phy_data.media_active || cmd == MiiPhyCmd::MediaChg {
        mii.on_state_change(mii_data);
        phy_data.media_active = mii_data.media_active;
    }

    if mii_data.media_status != phy_data.media_status {
        miibus_linkchg(mii_data);
        phy_data.media_status = mii_data.media_status;
    }

    Ok(())
}
