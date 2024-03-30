//! Media-independent interface (MII) driver.

use alloc::{boxed::Box, collections::BTreeMap};
use awkernel_lib::net::net_device::LinkStatus;
use bitflags::bitflags;

use crate::if_media::{Ifmedia, Media, IFM_ACTIVE, IFM_AUTO, IFM_AVALID, IFM_ETHER, IFM_IMASK};

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

const MII_ANAR: u32 = 0x04; // Autonegotiation advertisement (rw)
const ANAR_NP: u32 = 0x8000; // Next page (ro)
const ANAR_ACK: u32 = 0x4000; // link partner abilities acknowledged (ro)
const ANAR_RF: u32 = 0x2000; // remote fault (ro)
const ANAR_FC: u32 = 0x0400; // local device supports PAUSE
const ANAR_T4: u32 = 0x0200; // local device supports 100bT4
const ANAR_TX_FD: u32 = 0x0100; // local device supports 100bTx FD
const ANAR_TX: u32 = 0x0080; // local device supports 100bTx
const ANAR_10_FD: u32 = 0x0040; // local device supports 10bT FD
const ANAR_10: u32 = 0x0020; // local device supports 10bT
const ANAR_CSMA: u32 = 0x0001; // protocol selector CSMA/CD
const ANAR_PAUSE_NONE: u32 = 0;
const ANAR_PAUSE_SYM: u32 = 1 << 10;
const ANAR_PAUSE_ASYM: u32 = 2 << 10;
const ANAR_PAUSE_TOWARDS: u32 = 3 << 10;

const MII_ANLPAR: u32 = 0x05; // Autonegotiation link partner abilities (ro)
const ANLPAR_NP: u32 = 0x8000; // Next page (ro)
const ANLPAR_ACK: u32 = 0x4000; // link partner accepted ACK (ro)
const ANLPAR_RF: u32 = 0x2000; // remote fault (ro)
const ANLPAR_FC: u32 = 0x0400; // link partner supports PAUSE
const ANLPAR_T4: u32 = 0x0200; // link partner supports 100bT4
const ANLPAR_TX_FD: u32 = 0x0100; // link partner supports 100bTx FD
const ANLPAR_TX: u32 = 0x0080; // link partner supports 100bTx
const ANLPAR_10_FD: u32 = 0x0040; // link partner supports 10bT FD
const ANLPAR_10: u32 = 0x0020; // link partner supports 10bT
const ANLPAR_CSMA: u32 = 0x0001; // protocol selector CSMA/CD
const ANLPAR_PAUSE_MASK: u32 = 3 << 10;
const ANLPAR_PAUSE_NONE: u32 = 0 << 10;
const ANLPAR_PAUSE_SYM: u32 = 1 << 10;
const ANLPAR_PAUSE_ASYM: u32 = 2 << 10;
const ANLPAR_PAUSE_TOWARDS: u32 = 3 << 10;

// This is the 1000baseT control register
const MII_100T2CR: u32 = 0x09; // 100base-T2 control register
const GTCR_TEST_MASK: u32 = 0xe000; // see 802.3ab ss.
const GTCR_MAN_MS: u32 = 0x1000; // enable manual master/slave control
const GTCR_ADV_MS: u32 = 0x0800; // 1 = adv. master, 0 = adv. slave
const GTCR_PORT_TYPE: u32 = 0x0400; // 1 = DCE, 0 = DTE (NIC)
const GTCR_ADV_1000TFDX: u32 = 0x0200; // adv. 1000baseT FDX
const GTCR_ADV_1000THDX: u32 = 0x0100; // adv. 1000baseT HDX

// This is also the 1000baseT status register
const MII_100T2SR: u32 = 0x0a; // 100base-T2 status register
const GTSR_MAN_MS_FLT: u32 = 0x8000; // master/slave config fault
const GTSR_MS_RES: u32 = 0x4000; // result: 1 = master, 0 = slave
const GTSR_LRS: u32 = 0x2000; // local rx status, 1 = ok
const GTSR_RRS: u32 = 0x1000; // remote rx status, 1 = ok
const GTSR_LP_1000TFDX: u32 = 0x0800; // link partner 1000baseT FDX capable
const GTSR_LP_1000THDX: u32 = 0x0400; // link partner 1000baseT HDX capable
const GTSR_LP_ASM_DIR: u32 = 0x0200; // link partner asym. pause dir. capable
const GTSR_IDLE_ERR: u32 = 0x00ff; // IDLE error count

const MII_ANEGTICKS: u32 = 5;
const MII_ANEGTICKS_GIGE: u32 = 17;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MiiError {
    Read,
    Write,
    InvalidParam,
    Media,
}

pub struct MiiDev {
    mii_data: MiiData,
    phys: BTreeMap<u32, Box<dyn MiiPhy + Send + Sync>>,
}

impl MiiDev {
    #[inline(always)]
    pub fn link_status(&self) -> LinkStatus {
        self.mii_data.link_state
    }

    /// Get the current link speed in Mbps.
    #[inline(always)]
    pub fn link_speed(&self) -> u64 {
        self.mii_data.media_active.link_speed()
    }
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

    fn on_state_change(&mut self, mii_data: &MiiData);
}

pub struct MiiData {
    flags: MiiFlags,
    instance: u32,
    media: Ifmedia,
    media_active: Media,
    media_status: Media,
    link_state: LinkStatus,
}

impl MiiData {
    #[inline(always)]
    pub fn get_media_active(&self) -> Media {
        self.media_active
    }

    #[inline(always)]
    pub fn get_media_status(&self) -> Media {
        self.media_status
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MiiPhyCmd {
    PollStat,
    MediaChg,
    Tick,
}

pub trait MiiPhy {
    fn service(
        &mut self,
        mii: &mut dyn Mii,
        mii_data: &mut MiiData,
        cmd: MiiPhyCmd,
    ) -> Result<(), MiiError>;

    fn status(&self, mii: &mut dyn Mii, mii_data: &mut MiiData) -> Result<(), MiiError>;

    fn reset(&mut self, mii: &mut dyn Mii, mii_data: &mut MiiData) -> Result<(), MiiError>;

    fn get_phy_data(&self) -> &MiiPhyData;

    fn get_phy_data_mut(&mut self) -> &mut MiiPhyData;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MiiPhyMode {
    Unknown,
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
    media_active: Media,  // last active media
    media_status: Media,  // last active status
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
            media_active: Media::new(0),
            media_status: Media::new(0),
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
) -> Result<MiiDev, MiiError> {
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
        media_active: Media::new(0),
        media_status: Media::new(0),
        link_state: LinkStatus::Unknown,
    };

    let mut phys = BTreeMap::new();

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

        if let Ok(phy) = ukphy::attach(mii, &mut mii_data, args) {
            phys.insert(phy.get_phy_data().inst, phy);
        } else {
            log::error!("mii_attach: failed to attach PHY at address {}", phy);
        }
    }

    Ok(MiiDev { mii_data, phys })
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

fn miibus_linkchg(mii_data: &mut MiiData) {
    if mii_data.media_status.contains(IFM_AVALID) {
        if mii_data.media_status.contains(IFM_ACTIVE) {
            mii_data.link_state = LinkStatus::Up;
        } else {
            mii_data.link_state = LinkStatus::Down;
        }
    } else {
        mii_data.link_state = LinkStatus::Unknown;
    }

    log::debug!(
        "miibus_linkchg: link state {:?}, speed {}",
        mii_data.link_state,
        mii_data.media_active.link_speed()
    );
}

pub fn mii_tick(mii: &mut dyn Mii, mii_dev: &mut MiiDev) -> Result<(), MiiError> {
    let (mii_data, phys) = (&mut mii_dev.mii_data, &mut mii_dev.phys);

    let Some(media) = mii_data.media.get_current() else {
        return Ok(());
    };

    let inst = media.get_instance();

    if let Some(phy) = phys.get_mut(&inst) {
        phy.service(mii, mii_data, MiiPhyCmd::Tick)?;
    }

    Ok(())
}

pub fn mii_mediachg(mii: &mut dyn Mii, mii_dev: &mut MiiDev) -> Result<(), MiiError> {
    let (mii_data, phys) = (&mut mii_dev.mii_data, &mut mii_dev.phys);

    let Some(media) = mii_data.media.get_current() else {
        return Ok(());
    };

    let current_inst = media.get_instance();

    for (inst, phy) in phys.iter_mut() {
        if *inst != current_inst {
            let phyno = phy.get_phy_data().phy;
            let bmcr = mii.read_reg(phyno, MII_BMCR)?;
            mii.write_reg(phyno, MII_BMCR, bmcr | BMCR_ISO)?;
        }

        phy.service(mii, mii_data, MiiPhyCmd::MediaChg)?;
    }

    Ok(())
}
