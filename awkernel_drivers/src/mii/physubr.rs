use crate::if_media::{
    ifm_make_word, ifm_options, ifm_subtype, IfmediaEntry, IFM_1000_SX, IFM_1000_T, IFM_100_FX,
    IFM_100_T4, IFM_100_TX, IFM_10_T, IFM_ETH_MASTER, IFM_ETH_RXPAUSE, IFM_ETH_TXPAUSE, IFM_FDX,
    IFM_FLOW, IFM_HPNA_1, IFM_NONE,
};

use super::*;

#[derive(Debug)]
struct MiiMedia {
    bmcr: u32,
    anar: u32,
    gtcr: u32,
}

const MII_MEDIA_TABLE: [MiiMedia; 10] = [
    // None
    MiiMedia {
        bmcr: BMCR_ISO,
        anar: ANAR_CSMA,
        gtcr: 0,
    },
    // 10baseT
    MiiMedia {
        bmcr: BMCR_S10,
        anar: ANAR_CSMA | ANAR_10,
        gtcr: 0,
    },
    // 10baseT-FDX
    MiiMedia {
        bmcr: BMCR_S10 | BMCR_FDX,
        anar: ANAR_CSMA | ANAR_10_FD,
        gtcr: 0,
    },
    // 100baseT4
    MiiMedia {
        bmcr: BMCR_S100,
        anar: ANAR_CSMA | ANAR_T4,
        gtcr: 0,
    },
    // 100baseTX
    MiiMedia {
        bmcr: BMCR_S100,
        anar: ANAR_CSMA | ANAR_TX,
        gtcr: 0,
    },
    // 100baseTX-FDX
    MiiMedia {
        bmcr: BMCR_S100 | BMCR_FDX,
        anar: ANAR_CSMA | ANAR_TX_FD,
        gtcr: 0,
    },
    // 1000baseX
    MiiMedia {
        bmcr: BMCR_S1000,
        anar: ANAR_CSMA,
        gtcr: 0,
    },
    // 1000baseX-FDX
    MiiMedia {
        bmcr: BMCR_S1000 | BMCR_FDX,
        anar: ANAR_CSMA,
        gtcr: 0,
    },
    // 1000baseT
    MiiMedia {
        bmcr: BMCR_S1000,
        anar: ANAR_CSMA,
        gtcr: GTCR_ADV_1000THDX,
    },
    // 1000baseT-FDX
    MiiMedia {
        bmcr: BMCR_S1000,
        anar: ANAR_CSMA,
        gtcr: GTCR_ADV_1000TFDX,
    },
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MiiMediaType {
    None = 0,
    _10T,
    _10TFdx,
    _100T4,
    _100Tx,
    _100TxFdx,
    _1000X,
    _1000XFdx,
    _1000T,
    _1000TFdx,
}

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

    if phy_data.extcapabilities & EXTSR_MEDIAMASK != 0
        && phy_data.extcapabilities & EXTSR_1000XHDX != 0
    {
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

    let Some(ife) = mii_data.media.get_current() else {
        return Err(MiiError::Media);
    };

    let index = match ifm_subtype(&ife.media) {
        IFM_AUTO => {
            if mii.read_reg(phy_data.phy, MII_BMCR)? & BMCR_AUTOEN == 0
                || phy_data
                    .flags
                    .intersects(MiiFlags::DOPAUSE | MiiFlags::FORCEANEG)
            {
                phy_auto(mii, mii_data, phy)?;
            }

            return Ok(());
        }
        IFM_NONE => MiiMediaType::None,
        IFM_HPNA_1 => MiiMediaType::_10T,
        IFM_10_T => {
            let options = ifm_options(&ife.media);

            if options == IFM_FDX || options == IFM_FDX | IFM_FLOW {
                MiiMediaType::_10TFdx
            } else {
                MiiMediaType::_10T
            }
        }
        IFM_100_TX | IFM_100_FX => {
            let options = ifm_options(&ife.media);

            if options == IFM_FDX || options == IFM_FDX | IFM_FLOW {
                MiiMediaType::_100TxFdx
            } else {
                MiiMediaType::_100Tx
            }
        }
        IFM_100_T4 => MiiMediaType::_100T4,
        IFM_1000_SX => {
            let options = ifm_options(&ife.media);

            if options == IFM_FDX || options == IFM_FDX | IFM_FLOW {
                MiiMediaType::_1000XFdx
            } else {
                MiiMediaType::_1000X
            }
        }
        IFM_1000_T => {
            let options = ifm_options(&ife.media);

            if options == 0 || options == IFM_ETH_MASTER {
                MiiMediaType::_1000T
            } else if options == IFM_FDX
                || options == IFM_FDX | IFM_ETH_MASTER
                || options == IFM_FDX | IFM_FLOW
                || options == IFM_FDX | IFM_FLOW | IFM_ETH_MASTER
            {
                MiiMediaType::_1000TFdx
            } else {
                return Err(MiiError::Media);
            }
        }
        _ => {
            return Err(MiiError::Media);
        }
    };

    let entry = &MII_MEDIA_TABLE[index as usize];
    let mut anar = entry.anar;
    let bmcr = entry.bmcr;
    let mut gtcr = entry.gtcr;

    if ifm_subtype(&ife.media) == IFM_1000_T {
        gtcr |= GTCR_MAN_MS;

        if ife.media.contains(IFM_ETH_MASTER) {
            gtcr |= GTCR_ADV_MS;
        }
    }

    if ife.media.contains(IFM_FDX)
        && (ife.media.contains(IFM_FLOW) || phy_data.flags.contains(MiiFlags::FORCEPAUSE))
    {
        if phy_data.flags.contains(MiiFlags::IS_1000X) {
            anar |= ANAR_X_PAUSE_TOWARDS;
        } else {
            anar |= ANAR_FC;

            // XXX Only 1000BASE-T has PAUSE_ASYM?
            if phy_data.flags.contains(MiiFlags::HAVE_GTCR)
                && phy_data.extcapabilities & (EXTSR_1000THDX | EXTSR_1000TFDX) != 0
            {
                anar |= ANAR_X_PAUSE_ASYM;
            }
        }
    }

    mii.write_reg(phy_data.phy, MII_ANAR, anar)?;
    mii.write_reg(phy_data.phy, MII_BMCR, bmcr)?;
    if phy.get_phy_data().flags.contains(MiiFlags::HAVE_GTCR) {
        mii.write_reg(phy_data.phy, MII_100T2CR, gtcr)?;
    }

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
        return Ok(TickReturn::Continue);
    }

    // Read the status register twice; BMSR_LINK is latch-low.
    let reg = mii.read_reg(phy_data.phy, MII_BMSR)? | mii.read_reg(phy_data.phy, MII_BMSR)?;
    if reg & BMSR_LINK != 0 {
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

fn phy_auto(
    mii: &mut dyn Mii,
    mii_data: &MiiData,
    phy: &mut dyn MiiPhy,
) -> Result<TickReturn, MiiError> {
    let Some(ife) = mii_data.media.get_current() else {
        return Err(MiiError::Media);
    };

    // Check for 1000BASE-X.  Autonegotiation is a bit
    // different on such devices.
    let phy_data = phy.get_phy_data();

    if phy_data.flags.contains(MiiFlags::IS_1000X) {
        let mut anar = 0;

        if phy_data.extcapabilities & EXTSR_1000XFDX != 0 {
            anar |= ANAR_X_FD;
        }

        if phy_data.extcapabilities & EXTSR_1000XHDX != 0 {
            anar |= ANAR_X_HD;
        }

        if ife.media.contains(IFM_FLOW) || phy_data.flags.contains(MiiFlags::FORCEPAUSE) {
            anar |= ANAR_X_PAUSE_TOWARDS;
        }

        mii.write_reg(phy_data.phy, MII_ANAR, anar)?;
    } else {
        let mut anar = bmsr_media_to_anar(phy_data.capabilities) | ANAR_CSMA;

        if ife.media.contains(IFM_FLOW) || phy_data.flags.contains(MiiFlags::FORCEPAUSE) {
            if phy_data.capabilities & (BMSR_10TFDX | BMSR_100TXFDX) != 0 {
                anar |= ANAR_FC;
            }

            // XXX Only 1000BASE-T has PAUSE_ASYM?
            if phy_data.flags.contains(MiiFlags::HAVE_GTCR)
                && phy_data.extcapabilities & (EXTSR_1000THDX | EXTSR_1000TFDX) != 0
            {
                anar |= ANAR_X_PAUSE_ASYM;
            }
        }

        mii.write_reg(phy_data.phy, MII_ANAR, anar)?;

        if phy_data.flags.contains(MiiFlags::HAVE_GTCR) {
            let mut gtcr = 0;

            if phy_data.extcapabilities & EXTSR_1000TFDX != 0 {
                gtcr |= GTCR_ADV_1000TFDX;
            }

            if phy_data.extcapabilities & EXTSR_1000THDX != 0 {
                gtcr |= GTCR_ADV_1000THDX;
            }

            mii.write_reg(phy_data.phy, MII_100T2CR, gtcr)?;
        }
    }

    mii.write_reg(phy_data.phy, MII_BMCR, BMCR_AUTOEN | BMCR_STARTNEG)?;

    Ok(TickReturn::JustReturn)
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
