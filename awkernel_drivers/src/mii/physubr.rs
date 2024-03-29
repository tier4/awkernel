use crate::if_media::{
    ifm_make_word, IfmediaEntry, IFM_1000_SX, IFM_1000_T, IFM_100_T4, IFM_100_TX, IFM_10_T,
    IFM_ETH_MASTER, IFM_FDX, IFM_FLOW, IFM_HPNA_1, IFM_NONE,
};

use super::*;

pub fn dev_attach(
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

    add_media(mii_data, phy);
    mii.media_init(mii_data)?;

    let phy_data = phy.get_phy_data_mut();

    // If maxspeed was specified we have to restart autonegotiation.
    // PHY might have attempted it and failed due to having mistakenly
    // advertising modes that we do not in fact support.
    if phy_data.maxspeed != 0 {
        phy_data.flags |= MiiFlags::FORCEANEG;
        // TODO: mii_phy_setmedia(sc);
        phy_data.flags &= !MiiFlags::FORCEANEG;
    }

    log::debug!("mii_data = {:?}", mii_data);

    Ok(())
}

pub fn reset(mii: &mut dyn Mii, mii_data: &MiiData, phy: &mut dyn MiiPhy) -> Result<(), MiiError> {
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

fn add_media(mii_data: &mut MiiData, phy: &mut dyn MiiPhy) {
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
