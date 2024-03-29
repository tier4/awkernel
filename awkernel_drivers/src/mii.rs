//! Media-independent interface (MII) driver.

use bitflags::bitflags;

use crate::if_media::{Ifmedia, Media, IFM_AUTO, IFM_ETHER, IFM_IMASK};

pub mod physubr;
pub mod ukphy;

pub const MIIF_RX_DELAY: u32 = 0x00000800; // add RX delay
pub const MIIF_TX_DELAY: u32 = 0x00001000; // add TX delay

// Special `locators' passed to mii_attach().  If one of these is not
// an `any' value, we look for *that* PHY and configure it.  If both
// are not `any', that is an error, and mii_attach() will fail.
pub const MII_OFFSET_ANY: u32 = 0xffffffff;
pub const MII_PHY_ANY: u32 = 0xffffffff;

const MII_NPHY: u32 = 32; // max # of PHYs per MII

const MII_BMCR: u32 = 0x00; // Basic mode control register (rw)
const BMCR_RESET: u32 = 0x8000; // reset
const BMCR_LOOP: u32 = 0x4000; // loopback
const BMCR_SPEED0: u32 = 0x2000; // speed selection (LSB)
const BMCR_AUTOEN: u32 = 0x1000; // autonegotiation enable
const BMCR_PDOWN: u32 = 0x0800; // power down
const BMCR_ISO: u32 = 0x0400; // isolate
const BMCR_STARTNEG: u32 = 0x0200; // restart autonegotiation
const BMCR_FDX: u32 = 0x0100; // Set duplex mode
const BMCR_CTEST: u32 = 0x0080; // collision test
const BMCR_SPEED1: u32 = 0x0040; // speed selection (MSB)

const MII_BMSR: u32 = 0x01; // Basic mode status register (ro)
const BMSR_100T4: u32 = 0x8000; // 100 base T4 capable
const BMSR_100TXFDX: u32 = 0x4000; // 100 base Tx full duplex capable
const BMSR_100TXHDX: u32 = 0x2000; // 100 base Tx half duplex capable
const BMSR_10TFDX: u32 = 0x1000; // 10 base T full duplex capable
const BMSR_10THDX: u32 = 0x0800; // 10 base T half duplex capable
const BMSR_100T2FDX: u32 = 0x0400; // 100 base T2 full duplex capable
const BMSR_100T2HDX: u32 = 0x0200; // 100 base T2 half duplex capable
const BMSR_EXTSTAT: u32 = 0x0100; // Extended status in register 15
const BMSR_MFPS: u32 = 0x0040; // MII Frame Preamble Suppression
const BMSR_ACOMP: u32 = 0x0020; // Autonegotiation complete
const BMSR_RFAULT: u32 = 0x0010; // Link partner fault
const BMSR_ANEG: u32 = 0x0008; // Autonegotiation capable
const BMSR_LINK: u32 = 0x0004; // Link status
const BMSR_JABBER: u32 = 0x0002; // Jabber detected
const BMSR_EXTCAP: u32 = 0x0001; // Extended capability

// Note that the EXTSTAT bit indicates that there is extended status
// info available in register 15, but 802.3 section 22.2.4.3 also
// states that all 1000 Mb/s capable PHYs will set this bit to 1.
const BMSR_MEDIAMASK: u32 = BMSR_100T4
    | BMSR_100TXFDX
    | BMSR_100TXHDX
    | BMSR_10TFDX
    | BMSR_10THDX
    | BMSR_100T2FDX
    | BMSR_100T2HDX;

const MII_PHYIDR1: u32 = 0x02; // ID register 1 (ro)

const MII_PHYIDR2: u32 = 0x03; // ID register 2 (ro)
const IDR2_OUILSB: u32 = 0xfc00; // OUI LSB
const IDR2_MODEL: u32 = 0x03f0; // vendor model
const IDR2_REV: u32 = 0x000f; // vendor revision

const MII_EXTSR: u32 = 0x0f; // Extended status register
const EXTSR_1000XFDX: u32 = 0x8000; // 1000X full-duplex capable
const EXTSR_1000XHDX: u32 = 0x4000; // 1000X half-duplex capable
const EXTSR_1000TFDX: u32 = 0x2000; // 1000T full-duplex capable
const EXTSR_1000THDX: u32 = 0x1000; // 1000T half-duplex capable

const EXTSR_MEDIAMASK: u32 = EXTSR_1000XFDX | EXTSR_1000XHDX | EXTSR_1000TFDX | EXTSR_1000THDX;

const MII_ANEGTICKS: u32 = 5;
const MII_ANEGTICKS_GIGE: u32 = 17;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MiiError {
    Read,
    Write,
    InvalidParam,
    Media,
}

pub trait Mii {
    /// Read a register from the PHY.
    fn read_reg(&mut self, phy: u32, reg: u32) -> Result<u32, MiiError>;

    /// Write a register to the PHY.
    fn write_reg(&mut self, phy: u32, reg: u32, data: u32) -> Result<(), MiiError>;

    fn media_init(&mut self, mii_data: &mut MiiData) -> Result<(), MiiError> {
        if mii_data.media.set_current_media(IFM_ETHER | IFM_AUTO) {
            Ok(())
        } else {
            Err(MiiError::Media)
        }
    }
}

#[derive(Debug)]
pub struct MiiData {
    flags: MiiFlags,
    instance: u32,
    media: Ifmedia,
}

pub trait MiiPhy {
    fn service(&mut self, mii: &mut dyn Mii) -> Result<(), MiiError>;

    fn status(&self, mii: &mut dyn Mii) -> u32;

    fn reset(&mut self, mii: &mut dyn Mii, mii_data: &mut MiiData) -> Result<(), MiiError>;

    fn get_phy_data(&self) -> &MiiPhyData;

    fn get_phy_data_mut(&mut self) -> &mut MiiPhyData;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MiiPhyMode {
    RgmiiId,
    RgmiiRxId,
    RgmiiTxId,
    Rgmii,
}

#[derive(Debug)]
pub struct MiiAttachArgs {
    phyno: u32,   // MII address
    offset: u32,  // first PHY, second PHY, etc.
    id1: u32,     // PHY ID register 1
    id2: u32,     // PHY ID register 2
    capmask: u32, // capability mask for BMSR
}

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct MiiFlags: u32 {
        const INITDONE = 0x00000001; // has been initialized (mii_data)
        const NOISOLATE = 0x00000002; // do not isolate the PHY
        const DOINGAUTO = 0x00000008; // doing autonegotiation (mii_softc)
        const AUTOTSLEEP = 0x00000010; // use tsleep(), not callout()
        const HAVEFIBER = 0x00000020; // from parent: has fiber interface
        const HAVE_GTCR = 0x00000040; // has 100base-T2/1000base-T CR
        const IS_1000X = 0x00000080; // is a 1000BASE-X device
        const DOPAUSE = 0x00000100; // advertise PAUSE capability
        const IS_HPNA = 0x00000200; // is a HomePNA device
        const FORCEANEG = 0x00000400; // force auto-negotiation
        const RX_DELAY = 0x00000800; // add RX delay
        const TX_DELAY = 0x00001000; // add TX delay
        const NOMANPAUSE = 0x00100000; // no manual PAUSE selection
        const FORCEPAUSE = 0x00200000; // force PAUSE advertisement
        const MACPRIV0 = 0x01000000; // private to the MAC driver
        const MACPRIV1 = 0x02000000; // private to the MAC driver
        const MACPRIV2 = 0x04000000; // private to the MAC driver
        const PHYPRIV0 = 0x10000000; // private to the PHY driver
        const PHYPRIV1 = 0x20000000; // private to the PHY driver
        const PHYPRIV2 = 0x40000000; // private to the PHY driver
    }
}

pub struct MiiPhyData {
    mpd_oui: u32,   // the PHY's OUI (MII_OUI())
    mpd_model: u32, // the PHY's model (MII_MODEL())
    mpd_rev: u32,   // the PHY's revision (MII_REV())
    capmask: u32,   // capability mask for BMSR
    phy: u32,       // our MII address
    offset: u32,    // first PHY, second PHY, etc.
    inst: u32,      // instance for ifmedia

    flags: MiiFlags,      // misc. flags
    capabilities: u32,    // capabilities from BMSR
    extcapabilities: u32, // extended capabilities
    ticks: u32,           // MII_TICK counter
    anegticks: u32,       // ticks before retrying aneg
    media_active: u32,    // last active media
    media_status: u32,    // last active status
    maxspeed: u32,        // Max speed supported by this PHY
}

impl MiiPhyData {
    pub fn new(mii_data: &mut MiiData, ma: &MiiAttachArgs) -> Self {
        let result = MiiPhyData {
            mpd_oui: mii_oui(ma.id1, ma.id2),
            mpd_model: mii_model(ma.id2),
            mpd_rev: mii_rev(ma.id2),
            capmask: ma.capmask,
            phy: ma.phyno,
            offset: ma.offset,
            inst: mii_data.instance,
            flags: mii_data.flags,
            capabilities: 0,
            extcapabilities: 0,
            ticks: 0,
            anegticks: 0,
            media_active: 0,
            media_status: 0,
            maxspeed: 0,
        };

        mii_data.instance += 1;

        result
    }
}

pub fn attach(
    mii: &mut dyn Mii,
    capmask: u32,
    phyloc: u32,
    offloc: u32,
    flags: MiiFlags,
) -> Result<(), MiiError> {
    if phyloc != MII_PHY_ANY && offloc != MII_OFFSET_ANY {
        log::debug!("mii_attach: phyloc and offloc are both not MII_ANY");
        return Err(MiiError::InvalidParam);
    }

    if offloc != MII_OFFSET_ANY && offloc >= MII_NPHY {
        log::debug!("mii_attach: invalid offloc {}", offloc);
        return Err(MiiError::InvalidParam);
    }

    let (phymin, phymax) = if phyloc == MII_PHY_ANY {
        (0, MII_NPHY - 1)
    } else if phyloc != MII_PHY_ANY && phyloc >= MII_NPHY {
        log::debug!("mii_attach: invalid phyloc {}", phyloc);
        return Err(MiiError::InvalidParam);
    } else {
        (phyloc, phyloc)
    };

    let mut mii_data = MiiData {
        flags,
        instance: 0,
        media: Ifmedia::new(IFM_IMASK, Media::new(0)),
    };

    for (offset, phy) in (phymin..=phymax).enumerate() {
        // Check to see if there is a PHY at this address.  Note,
        // many braindead PHYs report 0/0 in their ID registers,
        // so we test for media in the BMSR.
        let Ok(bmsr) = mii.read_reg(phy, MII_BMSR) else {
            continue;
        };

        if bmsr == 0 || bmsr == 0xffff || (bmsr & (BMSR_EXTSTAT | BMSR_MEDIAMASK)) == 0 {
            // Assume no PHY at this address.
            continue;
        }

        // There is a PHY at this address.  If we were given an
        // `offset' locator, skip this PHY if it doesn't match.
        if offloc != MII_OFFSET_ANY && offloc != offset as u32 {
            continue;
        }

        // Extract the IDs.  Braindead PHYs will be handled by
        // the `ukphy' driver, as we have no ID information to
        // match on.
        let mii_id1 = mii.read_reg(phy, MII_PHYIDR1)?;
        let mii_id2 = mii.read_reg(phy, MII_PHYIDR2)?;

        let args = MiiAttachArgs {
            phyno: phy,
            offset: offset as u32,
            id1: mii_id1,
            id2: mii_id2,
            capmask,
        };

        if let Err(e) = ukphy::attach(mii, &mut mii_data, args) {
            log::error!("mii_attach: ukphy::attach failed: {:?}", e);
        }
    }

    Ok(())
}

#[inline(always)]
fn mii_oui(id1: u32, id2: u32) -> u32 {
    (id1 << 6) | (id2 >> 10)
}

#[inline(always)]
fn mii_model(id2: u32) -> u32 {
    (id2 & IDR2_MODEL) >> 4
}

#[inline(always)]
fn mii_rev(id2: u32) -> u32 {
    id2 & IDR2_REV
}
