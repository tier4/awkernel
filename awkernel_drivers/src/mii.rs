//! # Media-independent interface (MII)

use core::fmt::Debug;

use alloc::{boxed::Box, collections::BTreeMap};
use awkernel_lib::net::net_device::LinkStatus;
use bitflags::bitflags;

use crate::if_media::*;

pub mod ukphy;

bitflags! {
    #[derive(Debug, Clone, Copy)]
    pub struct MiiFlags: u16 {
        const INITDONE = 0x0001; // has been initialized (mii_data)
        const NOISOLATE = 0x0002; // do not isolate the PHY
        const NOLOOP = 0x0004; // no loopback capability
        const DOINGAUTO = 0x0008; // doing autonegotiation (mii_softc)
        const AUTOTSLEEP = 0x0010; // use tsleep(), not timeout()
        const HAVEFIBER = 0x0020; // from parent: has fiber interface
        const HAVE_GTCR = 0x0040; // has 100base-T2/1000base-T CR
        const IS_1000X = 0x0080; // is a 1000BASE-X device
        const DOPAUSE = 0x0100; // advertise PAUSE capability
        const IS_HPNA = 0x0200; // is a HomePNA device
        const FORCEANEG = 0x0400; // force autonegotiation
        const SETDELAY = 0x0800; // set internal delay
        const RXID = 0x1000; // add Rx delay
        const TXID = 0x2000; // add Tx delay
        const SGMII = 0x4000; // MAC to PHY interface is SGMII
    }
}

pub const IDR2_MODEL: u32 = 0x03f0; // vendor model
pub const IDR2_REV: u32 = 0x000f; // vendor revision

pub const MII_BMCR: u32 = 0x00; // Basic mode control register (rw)
pub const BMCR_RESET: u32 = 0x8000; // reset
pub const BMCR_LOOP: u32 = 0x4000; // loopback
pub const BMCR_SPEED0: u32 = 0x2000; // speed selection (LSB)
pub const BMCR_AUTOEN: u32 = 0x1000; // autonegotiation enable
pub const BMCR_PDOWN: u32 = 0x0800; // power down
pub const BMCR_ISO: u32 = 0x0400; // isolate
pub const BMCR_STARTNEG: u32 = 0x0200; // restart autonegotiation
pub const BMCR_FDX: u32 = 0x0100; // Set duplex mode
pub const BMCR_CTEST: u32 = 0x0080; // collision test
pub const BMCR_SPEED1: u32 = 0x0040; // speed selection (MSB)

pub const BMCR_S10: u32 = 0x0000; // 10 Mb/s
pub const BMCR_S100: u32 = BMCR_SPEED0; // 100 Mb/s
pub const BMCR_S1000: u32 = BMCR_SPEED1; // 1000 Mb/s

pub const MII_BMSR: u32 = 0x01; // Basic mode status register (ro)
pub const MII_PHYIDR1: u32 = 0x02; // ID register 1 (ro)
pub const MII_PHYIDR2: u32 = 0x03; // ID register 2 (ro)

pub const MII_ANAR: u32 = 0x04; // Autonegotiation advertisement (rw)
pub const ANAR_PAUSE_SYM: u32 = 1 << 10;
pub const ANAR_PAUSE_ASYM: u32 = 2 << 10;
pub const ANAR_PAUSE_TOWARDS: u32 = 3 << 10;

pub const MII_ANLPAR: u32 = 0x05; // Autonegotiation lnk partner abilities (rw)
pub const ANLPAR_T4: u32 = 0x0200; // link partner supports 100bT4
pub const ANLPAR_TX_FD: u32 = 0x0100; // link partner supports 100bTx FD
pub const ANLPAR_TX: u32 = 0x0080; // link partner supports 100bTx
pub const ANLPAR_10_FD: u32 = 0x0040; // link partner supports 10bT FD
pub const ANLPAR_10: u32 = 0x0020; // link partner supports 10bT
pub const ANLPAR_PAUSE_NONE: u32 = 0 << 10;
pub const ANLPAR_PAUSE_SYM: u32 = 1 << 10;
pub const ANLPAR_PAUSE_ASYM: u32 = 2 << 10;
pub const ANLPAR_PAUSE_TOWARDS: u32 = 3 << 10;

pub const ANAR_FC: u32 = 0x0400; // local device supports PAUSE
pub const ANAR_T4: u32 = 0x0200; // local device supports 100bT4
pub const ANAR_TX_FD: u32 = 0x0100; // local device supports 100bTx FD
pub const ANAR_TX: u32 = 0x0080; // local device supports 100bTx
pub const ANAR_10_FD: u32 = 0x0040; // local device supports 10bT FD
pub const ANAR_10: u32 = 0x0020; // local device supports 10bT
pub const ANAR_CSMA: u32 = 0x0001; // protocol selector CSMA/CD

pub const ANAR_X_FD: u32 = 0x0020; // local device supports 1000BASE-X FD
pub const ANAR_X_HD: u32 = 0x0040; // local device supports 1000BASE-X HD
pub const ANAR_X_PAUSE_NONE: u32 = 0 << 7;
pub const ANAR_X_PAUSE_SYM: u32 = 1 << 7;
pub const ANAR_X_PAUSE_ASYM: u32 = 2 << 7;
pub const ANAR_X_PAUSE_TOWARDS: u32 = 3 << 7;

pub const MII_NPHY: u32 = 32; // max # of PHYs per MII

pub const MII_100T2CR: u32 = 0x09; // 100base-T2 control register
pub const GTCR_TEST_MASK: u32 = 0xe000; // see 802.3ab ss. 40.6.1.1.2
pub const GTCR_MAN_MS: u32 = 0x1000; // enable manual master/slave control
pub const GTCR_ADV_MS: u32 = 0x0800; // 1 = adv. master, 0 = adv. slave
pub const GTCR_PORT_TYPE: u32 = 0x0400; // 1 = DCE, 0 = DTE (NIC)
pub const GTCR_ADV_1000TFDX: u32 = 0x0200; // adv. 1000baseT FDX
pub const GTCR_ADV_1000THDX: u32 = 0x0100; // adv. 1000baseT HDX

pub const MII_100T2SR: u32 = 0x0a; // 100base-T2 status register
pub const GTSR_MAN_MS_FLT: u32 = 0x8000; // master/slave config fault
pub const GTSR_MS_RES: u32 = 0x4000; // result: 1 = master, 0 = slave
pub const GTSR_LRS: u32 = 0x2000; // local rx status, 1 = ok
pub const GTSR_RRS: u32 = 0x1000; // remove rx status, 1 = ok
pub const GTSR_LP_1000TFDX: u32 = 0x0800; // link partner 1000baseT FDX capable
pub const GTSR_LP_1000THDX: u32 = 0x0400; // link partner 1000baseT HDX capable
pub const GTSR_LP_ASM_DIR: u32 = 0x0200; // link partner asym. pause dir. capable
pub const GTSR_IDLE_ERR: u32 = 0x00ff; // IDLE error count

bitflags! {
    #[derive(Debug, Clone, Copy)]
    pub struct BMSR: u32 {
        const ETH_100T4 = 0x8000; // 100 base T4 capable
        const ETH_100TXFDX = 0x4000; // 100 base Tx full duplex capable
        const ETH_100TXHDX = 0x2000; // 100 base Tx half duplex capable
        const ETH_10TFDX = 0x1000; // 10 base T full duplex capable
        const ETH_10THDX = 0x0800; // 10 base T half duplex capable
        const ETH_100T2FDX = 0x0400; // 100 base T2 full duplex capable
        const ETH_100T2HDX = 0x0200; // 100 base T2 half duplex capable
        const EXTSTAT = 0x0100; // Extended status in register 15
        const MFPS = 0x0040; // MII Frame Preamble Suppression
        const ACOMP = 0x0020; // Autonegotiation complete
        const RFAULT = 0x0010; // Link partner fault
        const ANEG = 0x0008; // Autonegotiation capable
        const LINK = 0x0004; // Link status
        const JABBER = 0x0002; // Jabber detected
        const EXTCAP = 0x0001; // Extended capability
    }
}

#[inline(always)]
fn bmsr_media_mask() -> BMSR {
    BMSR::ETH_100T4
        | BMSR::ETH_100TXFDX
        | BMSR::ETH_100TXHDX
        | BMSR::ETH_10TFDX
        | BMSR::ETH_10THDX
        | BMSR::ETH_100T2FDX
        | BMSR::ETH_100T2HDX
}

pub const MII_EXTSR: u32 = 0x0f; // Extended status register

bitflags! {
    #[derive(Debug, Clone, Copy)]
    pub struct EXTSR: u32 {
        const ETH_1000XFDX = 0x8000; // 1000X full-duplex capable
        const ETH_1000XHDX = 0x4000; // 1000X half-duplex capable
        const ETH_1000TFDX = 0x2000; // 1000T full-duplex capable
        const ETH_1000THDX = 0x1000; // 1000T half-duplex capable
    }
}

#[inline(always)]
pub fn extsr_media_mask() -> EXTSR {
    EXTSR::ETH_1000XFDX | EXTSR::ETH_1000XHDX | EXTSR::ETH_1000TFDX | EXTSR::ETH_1000THDX
}

pub const MII_MEDIA_NONE: u32 = 0;
pub const MII_MEDIA_10_T: u32 = 1;
pub const MII_MEDIA_10_T_FDX: u32 = 2;
pub const MII_MEDIA_100_T4: u32 = 3;
pub const MII_MEDIA_100_TX: u32 = 4;
pub const MII_MEDIA_100_TX_FDX: u32 = 5;
pub const MII_MEDIA_1000_X: u32 = 6;
pub const MII_MEDIA_1000_X_FDX: u32 = 7;
pub const MII_MEDIA_1000_T: u32 = 8;
pub const MII_MEDIA_1000_T_FDX: u32 = 9;
pub const MII_NMEDIA: u32 = 10;

pub const MII_ANEGTICKS: u32 = 5;
pub const MII_ANEGTICKS_GIGE: u32 = 10;

/// An array of these structures map MII media types to BMCR/ANAR settings.
struct MiiMedia {
    mm_bmcr: u32, // BMCR settings for this media
    mm_anar: u32, // ANAR settings for this media
    mm_gtcr: u32, // 100base-T2 or 1000base-T CR
}

// Media to register setting conversion table.  Order matters.
// XXX 802.3 doesn't specify ANAR or ANLPAR bits for 1000base.
const MII_MEDIA_TABLE: [MiiMedia; 10] = [
    // None
    MiiMedia {
        mm_bmcr: BMCR_ISO,
        mm_anar: ANAR_CSMA,
        mm_gtcr: 0,
    },
    // 10baseT
    MiiMedia {
        mm_bmcr: BMCR_S10,
        mm_anar: ANAR_CSMA | ANAR_10,
        mm_gtcr: 0,
    },
    // 10baseT-FDX
    MiiMedia {
        mm_bmcr: BMCR_S10 | BMCR_FDX,
        mm_anar: ANAR_CSMA | ANAR_10_FD,
        mm_gtcr: 0,
    },
    // 100baseT4
    MiiMedia {
        mm_bmcr: BMCR_S100,
        mm_anar: ANAR_CSMA | ANAR_T4,
        mm_gtcr: 0,
    },
    // 100baseTX
    MiiMedia {
        mm_bmcr: BMCR_S100,
        mm_anar: ANAR_CSMA | ANAR_TX,
        mm_gtcr: 0,
    },
    // 100baseTX-FDX
    MiiMedia {
        mm_bmcr: BMCR_S100 | BMCR_FDX,
        mm_anar: ANAR_CSMA | ANAR_TX_FD,
        mm_gtcr: 0,
    },
    // 1000baseX
    MiiMedia {
        mm_bmcr: BMCR_S1000,
        mm_anar: ANAR_CSMA,
        mm_gtcr: 0,
    },
    // 1000baseX-FDX
    MiiMedia {
        mm_bmcr: BMCR_S1000 | BMCR_FDX,
        mm_anar: ANAR_CSMA,
        mm_gtcr: 0,
    },
    // 1000baseT
    MiiMedia {
        mm_bmcr: BMCR_S1000,
        mm_anar: ANAR_CSMA,
        mm_gtcr: GTCR_ADV_1000THDX,
    },
    // 1000baseT-FDX
    MiiMedia {
        mm_bmcr: BMCR_S1000 | BMCR_FDX,
        mm_anar: ANAR_CSMA,
        mm_gtcr: GTCR_ADV_1000TFDX,
    },
];

pub struct MiiData {
    flags: MiiFlags,
    phys: BTreeMap<u32, Box<dyn MiiPhy>>,

    current_phy: Option<(u32, Ifmedia)>,

    media_active: u64,
    media_status: u64,

    supported_media: MediaList,

    instance: u32,
}

impl MiiData {
    pub fn new(flags: MiiFlags) -> Self {
        Self {
            flags,
            phys: BTreeMap::new(),
            current_phy: None,

            media_active: 0,
            media_status: 0,

            supported_media: MediaList::new(),

            instance: 0,
        }
    }

    #[inline(always)]
    pub fn insert(&mut self, phy: Box<dyn MiiPhy>) {
        let phy_no = phy.get_attach_args().phy_no;
        self.phys.insert(phy_no, phy);
    }

    #[inline(always)]
    pub fn get_media_active(&self) -> u64 {
        self.media_active
    }

    /// Find the media with the most bits in common with the target.
    /// Make the media the current media.
    /// If no media is found, return false.
    pub fn set_active_media(&mut self, target: u64) -> bool {
        let Some(ifmedia) = self.supported_media.find(target) else {
            return false;
        };

        let instance = ifmedia.get_instance();

        for (_, phy) in self.phys.iter_mut() {
            let ma = phy.get_attach_args_mut();
            if ma.instance == instance {
                self.current_phy = Some((ma.phy_no, ifmedia.clone()));
                return true;
            }
        }

        false
    }

    #[inline(always)]
    pub fn link_status(&self) -> LinkStatus {
        if self.media_status & IFM_AVALID != 0 {
            if self.media_status & IFM_ACTIVE != 0 {
                if self.media_active & IFM_FDX != 0 {
                    LinkStatus::UpFullDuplex
                } else {
                    LinkStatus::UpHalfDuplex
                }
            } else {
                LinkStatus::Down
            }
        } else {
            LinkStatus::Unknown
        }
    }
}

#[derive(Debug)]
pub struct MiiAttachArgs {
    phy_no: u32,     // MII address
    id1: u32,        // PHY ID register 1
    id2: u32,        // PHY ID register 2
    capmask: u32,    // capability mask from BMSR
    flags: MiiFlags, // flags from parent.

    capabilities: BMSR,      // capabilities from BMSR
    ext_capabilities: EXTSR, // extended capabilities

    anegticks: u32, // ticks before retrying aneg
    ticks: u32,

    media_active: u64,
    media_status: u64,

    instance: u32, // instance number
}

pub trait Mii {
    fn read_reg(&mut self, phy: u32, reg: u32) -> Result<u32, MiiError>;
    fn write_reg(&mut self, phy: u32, reg: u32, val: u32);

    fn stat_change(&mut self) -> Result<(), MiiError>;

    fn get_data(&self) -> &MiiData;
    fn get_data_mut(&mut self) -> &mut MiiData;
}

pub trait MiiPhy: Send + Sync + Debug {
    /// # The Service routine of the PHY.
    ///
    /// `parent` is the parent device.
    /// `ma` is the PHY's attach args.
    fn service(&mut self, parent: &mut dyn Mii, opcode: MiiOpCode) -> Result<(), MiiError>;

    /// `parent` is the parent device.
    fn status(&mut self, parent: &mut dyn Mii) -> Result<(), MiiError>;

    /// `parent` is the parent device.
    fn reset(&mut self, parent: &mut dyn Mii) -> Result<(), MiiError> {
        let ma = self.get_attach_args_mut();

        let reg = if ma.flags.contains(MiiFlags::NOISOLATE) {
            BMCR_RESET
        } else {
            BMCR_RESET | BMCR_ISO
        };

        parent.write_reg(ma.phy_no, MII_BMCR, reg);

        // It is best to allow a little time for the reset to settle
        // in before we start polling the BMCR again.  Notably, the
        // DP83840A manual states that there should be a 500us delay
        // between asserting software reset and attempting MII serial
        // operations.  Also, a DP83815 can get into a bad state on
        // cable removal and reinsertion if we do not delay here.
        awkernel_lib::delay::wait_microsec(500);

        // Wait another 100ms for it to complete.
        for _ in 0..100 {
            let reg = parent.read_reg(ma.phy_no, MII_BMCR)?;
            if (reg & BMCR_RESET) == 0 {
                break;
            }
            awkernel_lib::delay::wait_microsec(1000);
        }

        if ma.instance != 0 && !ma.flags.contains(MiiFlags::NOISOLATE) {
            parent.write_reg(ma.phy_no, MII_BMCR, reg | BMCR_ISO);
        }

        Ok(())
    }

    fn attach(&mut self, parent: &mut dyn Mii) -> Result<(), MiiError>;

    fn get_attach_args(&self) -> &MiiAttachArgs;
    fn get_attach_args_mut(&mut self) -> &mut MiiAttachArgs;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MiiOpCode {
    Tick,        // once-per-second tick
    MediaChange, // user changed media; perform the switch
    PollStatus,  // user requested media status; fill it in
    Down,        // interface is down
}

#[derive(Debug, Clone, Copy)]
pub enum MiiError {
    ReadError,
    WriteError,
    IO,
}

pub fn attach<F>(
    mii: &mut impl Mii,
    phy_generator: F,
    capmask: u32,
    phyloc: Option<u32>,
    offloc: Option<u32>,
) -> Result<(), MiiError>
where
    F: Fn(MiiAttachArgs) -> Box<dyn MiiPhy>,
{
    if phyloc.is_some() && offloc.is_some() {
        panic!("mii_attach: phyloc and offloc specified");
    }

    let (phymin, phymax) = if let Some(phyloc) = phyloc {
        (phyloc, phyloc)
    } else {
        (0, MII_NPHY - 1)
    };

    let mut offset = 0;
    'outer: for mii_phyno in phymin..=phymax {
        // Make sure we haven't already configured a PHY at this
        // address.  This allows mii_attach() to be called
        // multiple times.
        for (phy, _) in mii.get_data().phys.iter() {
            if *phy == mii_phyno {
                // Yes, there is already something
                // configured at this address.
                offset += 1;
                continue 'outer;
            }
        }

        let bmsr = BMSR::from_bits_retain(mii.read_reg(mii_phyno, MII_BMSR)?);
        if bmsr.bits() == 0
            || bmsr.bits() == 0xffff
            || !bmsr.intersects(bmsr_media_mask() | BMSR::EXTSTAT)
        {
            // Assume no PHY at this address.
            continue 'outer;
        }

        // There is a PHY at this address.  If we were given an
        // `offset' locator, skip this PHY if it doesn't match.
        if let Some(offloc) = offloc {
            if offloc != offset {
                offset += 1;
                continue 'outer;
            }
        }

        // Extract the IDs.  Braindead PHYs will be handled by
        // the `ukphy' driver, as we have no ID information to
        // match on.
        let id1 = mii.read_reg(mii_phyno, MII_PHYIDR1)?;
        let id2 = mii.read_reg(mii_phyno, MII_PHYIDR2)?;

        log::debug!("MII: id1: {:#x}", id1);
        log::debug!("MII: id2: {:#x}", id2);

        let mii_data = mii.get_data();

        let ma = MiiAttachArgs {
            phy_no: mii_phyno,
            id1,
            id2,
            capmask,
            flags: mii_data.flags,
            media_active: 0,
            media_status: 0,
            capabilities: BMSR::empty(),
            ext_capabilities: EXTSR::empty(),
            anegticks: 0,
            ticks: 0,
            instance: mii_data.instance,
        };

        let mut phy = phy_generator(ma);

        phy.attach(mii)?;

        log::debug!("MII: phy attached. phy = {phy:?}");

        let mii_data = mii.get_data_mut();

        mii_data.phys.insert(mii_phyno, phy);
        mii_data.instance += 1;
    }

    log::debug!(
        "MII: supported_media = {:?}",
        mii.get_data().supported_media
    );

    Ok(())
}

/// Inform the PHYs that the interface is down.
pub fn mii_down(dev: &mut dyn Mii, mii_data: &mut MiiData) {
    for (_, phy) in mii_data.phys.iter_mut() {
        if let Err(e) = phy.service(dev, MiiOpCode::Down) {
            log::error!("mii_down: error: {:?}", e);
        }
    }
}

fn phy_down(ma: &mut MiiAttachArgs) {
    if ma.flags.contains(MiiFlags::DOINGAUTO) {
        ma.flags.remove(MiiFlags::DOINGAUTO);
        // timeout_del(&sc->mii_phy_timo);
    }
}

fn phy_flow_status(parent: &mut dyn Mii, ma: &mut MiiAttachArgs) -> Result<u64, MiiError> {
    if !ma.flags.contains(MiiFlags::DOPAUSE) {
        return Ok(0);
    }

    let mut anar = parent.read_reg(ma.phy_no, MII_ANAR)?;
    let mut anlpar = parent.read_reg(ma.phy_no, MII_ANLPAR)?;

    // For 1000baseX, the bits are in a different location.
    if ma.flags.contains(MiiFlags::IS_1000X) {
        anar <<= 3;
        anlpar <<= 3;
    }

    if (anar & ANAR_PAUSE_SYM) & (anlpar & ANLPAR_PAUSE_SYM) != 0 {
        return Ok(IFM_FLOW | IFM_ETH_TXPAUSE | IFM_ETH_RXPAUSE);
    }

    if (anar & ANAR_PAUSE_SYM) == 0 {
        if (anar & ANAR_PAUSE_ASYM) != 0 && (anlpar & ANLPAR_PAUSE_TOWARDS) == ANLPAR_PAUSE_TOWARDS
        {
            return Ok(IFM_FLOW | IFM_ETH_TXPAUSE);
        } else {
            return Ok(0);
        }
    }

    if (anar & ANAR_PAUSE_ASYM) == 0 {
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

/// Initialize generic PHY media based on BMSR, called when a PHY is
/// attached.
fn phy_add_media(parent: &mut dyn Mii, ma: &mut MiiAttachArgs) {
    let mii = parent.get_data_mut();

    if !ma.flags.contains(MiiFlags::NOISOLATE) {
        let media = ifm_make_word(IFM_ETHER, IFM_NONE, 0, ma.instance as u64);
        mii.supported_media.add(Ifmedia {
            media,
            data: MII_MEDIA_NONE,
        });
    }

    if ma.capabilities.contains(BMSR::ETH_10THDX) {
        let media = ifm_make_word(IFM_ETHER, IFM_10_T, 0, ma.instance as u64);
        mii.supported_media.add(Ifmedia {
            media,
            data: MII_MEDIA_10_T,
        });
    }

    if ma.capabilities.contains(BMSR::ETH_10TFDX) {
        let media = ifm_make_word(IFM_ETHER, IFM_10_T, IFM_FDX, ma.instance as u64);
        mii.supported_media.add(Ifmedia {
            media,
            data: MII_MEDIA_10_T_FDX,
        });
    }

    if ma.capabilities.contains(BMSR::ETH_100TXHDX) {
        let media = ifm_make_word(IFM_ETHER, IFM_100_TX, 0, ma.instance as u64);
        mii.supported_media.add(Ifmedia {
            media,
            data: MII_MEDIA_100_TX,
        });
    }

    if ma.capabilities.contains(BMSR::ETH_100TXFDX) {
        let media = ifm_make_word(IFM_ETHER, IFM_100_TX, IFM_FDX, ma.instance as u64);
        mii.supported_media.add(Ifmedia {
            media,
            data: MII_MEDIA_100_TX_FDX,
        });
    }

    if ma.capabilities.contains(BMSR::ETH_100T4) {
        let media = ifm_make_word(IFM_ETHER, IFM_100_T4, 0, ma.instance as u64);
        mii.supported_media.add(Ifmedia {
            media,
            data: MII_MEDIA_100_T4,
        });
    }

    if ma.ext_capabilities.intersects(extsr_media_mask()) {
        if ma.ext_capabilities.contains(EXTSR::ETH_1000XHDX) {
            ma.anegticks = MII_ANEGTICKS_GIGE;
            ma.flags |= MiiFlags::IS_1000X;
            let media = ifm_make_word(IFM_ETHER, IFM_1000_SX, 0, ma.instance as u64);
            mii.supported_media.add(Ifmedia {
                media,
                data: MII_MEDIA_1000_X,
            });
        }

        if ma.ext_capabilities.contains(EXTSR::ETH_1000XFDX) {
            ma.anegticks = MII_ANEGTICKS_GIGE;
            ma.flags |= MiiFlags::IS_1000X;
            let media = ifm_make_word(IFM_ETHER, IFM_1000_SX, IFM_FDX, ma.instance as u64);
            mii.supported_media.add(Ifmedia {
                media,
                data: MII_MEDIA_1000_X_FDX,
            });
        }

        // 1000baseT media needs to be able to manipulate
        // master/slave mode.  We set IFM_ETH_MASTER in
        // the "don't care mask" and filter it out when
        // the media is set.
        //
        // All 1000baseT PHYs have a 1000baseT control register.
        if ma.ext_capabilities.contains(EXTSR::ETH_1000THDX) {
            ma.anegticks = MII_ANEGTICKS_GIGE;
            ma.flags |= MiiFlags::HAVE_GTCR;
            let media = ifm_make_word(IFM_ETHER, IFM_1000_T, 0, ma.instance as u64);
            mii.supported_media.add(Ifmedia {
                media,
                data: MII_MEDIA_1000_T,
            });
        }

        if ma.ext_capabilities.contains(EXTSR::ETH_1000TFDX) {
            ma.anegticks = MII_ANEGTICKS_GIGE;
            ma.flags |= MiiFlags::HAVE_GTCR;
            let media = ifm_make_word(IFM_ETHER, IFM_1000_T, IFM_FDX, ma.instance as u64);
            mii.supported_media.add(Ifmedia {
                media,
                data: MII_MEDIA_1000_T_FDX,
            });
        }
    }

    if ma.capabilities.contains(BMSR::ANEG) {
        let media = ifm_make_word(IFM_ETHER, IFM_AUTO, 0, ma.instance as u64);
        mii.supported_media.add(Ifmedia {
            media,
            data: MII_NMEDIA,
        });
    }
}

fn phy_update(
    parent: &mut dyn Mii,
    ma: &mut MiiAttachArgs,
    opcode: MiiOpCode,
) -> Result<(), MiiError> {
    let mii = parent.get_data_mut();
    if ma.media_active != mii.media_active
        || ma.media_status != mii.media_status
        || opcode == MiiOpCode::MediaChange
    {
        let mii = parent.get_data_mut();
        ma.media_active = mii.media_active;
        ma.media_status = mii.media_status;

        parent.stat_change()?;
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

/// Call the PHY tick routines, used during autonegotiation.
pub fn mii_tick(parent: &mut dyn Mii) -> Result<(), MiiError> {
    let mii = parent.get_data_mut();
    let mut tmp = BTreeMap::new();
    core::mem::swap(&mut tmp, &mut mii.phys);

    for (_, phy) in tmp.iter_mut() {
        if let Err(e) = phy.service(parent, MiiOpCode::Tick) {
            log::error!("mii_tick: error: {:?}", e);
        }
    }

    let mii = parent.get_data_mut();
    core::mem::swap(&mut tmp, &mut mii.phys);

    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum JustReturn {
    Yes,
    No,
}

fn phy_tick(parent: &mut dyn Mii, phy: &mut dyn MiiPhy) -> Result<JustReturn, MiiError> {
    // If we're not doing autonegotiation, we don't need to do
    // any extra work here.  However, we need to check the link
    // status so we can generate an announcement if the status
    // changes.
    let Some(current_phy) = &parent.get_data().current_phy else {
        return Ok(JustReturn::No);
    };

    if ifm_subtype(current_phy.1.media) != IFM_AUTO {
        return Ok(JustReturn::No);
    }

    let ma = phy.get_attach_args_mut();

    // Read the status register twice; BMSR_LINK is latch-low.
    let reg = BMSR::from_bits_retain(
        parent.read_reg(ma.phy_no, MII_BMSR)? | parent.read_reg(ma.phy_no, MII_BMSR)?,
    );

    if reg.contains(BMSR::LINK) {
        return Ok(JustReturn::No);
    }

    if ma.anegticks == 0 {
        ma.anegticks = MII_ANEGTICKS;
    }

    ma.ticks += 1;

    if ma.ticks <= ma.anegticks {
        return Ok(JustReturn::Yes); // EJUSTRETURN
    }

    ma.ticks = 0;

    phy.reset(parent)?;

    if phy_auto(parent, phy, false)? == JustReturn::Yes {
        return Ok(JustReturn::Yes); // EJUSTRETURN
    }

    // Might need to generate a status message if autonegotiation
    // failed.
    Ok(JustReturn::No)
}

fn phy_auto(
    parent: &mut dyn Mii,
    phy: &mut dyn MiiPhy,
    waitfor: bool,
) -> Result<JustReturn, MiiError> {
    let ma = phy.get_attach_args_mut();

    if !ma.flags.contains(MiiFlags::DOINGAUTO) {
        // Check for 1000BASE-X.  Autonegotiation is a bit
        // different on such devices.
        if ma.flags.contains(MiiFlags::IS_1000X) {
            let mut anar = 0;

            if ma.ext_capabilities.contains(EXTSR::ETH_1000XFDX) {
                anar |= ANAR_X_FD;
            }

            if ma.ext_capabilities.contains(EXTSR::ETH_1000XHDX) {
                anar |= ANAR_X_HD;
            }

            if ma.flags.contains(MiiFlags::DOPAUSE)
                && ma.ext_capabilities.contains(EXTSR::ETH_1000XFDX)
            {
                anar |= ANAR_X_PAUSE_TOWARDS;
            }

            parent.write_reg(ma.phy_no, MII_ANAR, anar);
        } else {
            let mut anar = bmsr_media_to_anar(ma.capabilities) | ANAR_CSMA;

            // Most 100baseTX PHY's only support symmetric
            // PAUSE, so we don't advertise asymmetric
            // PAUSE unless we also have 1000baseT capability.
            if ma.flags.contains(MiiFlags::DOPAUSE) {
                if ma.capabilities.contains(BMSR::ETH_100TXFDX) {
                    anar |= ANAR_FC;
                }

                if ma.ext_capabilities.contains(EXTSR::ETH_1000TFDX) {
                    anar |= ANAR_PAUSE_TOWARDS;
                }
            }

            parent.write_reg(ma.phy_no, MII_ANAR, anar);

            if ma.flags.contains(MiiFlags::HAVE_GTCR) {
                let mut gtcr = 0;

                if ma.ext_capabilities.contains(EXTSR::ETH_1000TFDX) {
                    gtcr |= GTCR_ADV_1000TFDX;
                }

                if ma.ext_capabilities.contains(EXTSR::ETH_1000THDX) {
                    gtcr |= GTCR_ADV_1000THDX;
                }

                parent.write_reg(ma.phy_no, MII_100T2CR, gtcr);
            }
        }
        parent.write_reg(ma.phy_no, MII_BMCR, BMCR_AUTOEN | BMCR_STARTNEG);
    }

    if waitfor {
        for _ in 0..500 {
            // Wait 500ms for it to complete.
            let bmsr = BMSR::from_bits_retain(parent.read_reg(ma.phy_no, MII_BMSR)?);
            if bmsr.contains(BMSR::ACOMP) {
                return Ok(JustReturn::No);
            }
            awkernel_lib::delay::wait_microsec(1000);
        }

        return Err(MiiError::IO);
    }

    // Just let it finish asynchronously.  This is for the benefit of
    // the tick handler driving autonegotiation.  Don't want 500ms
    // delays all the time while the system is running!
    if ma.flags.contains(MiiFlags::AUTOTSLEEP) {
        ma.flags |= MiiFlags::DOINGAUTO;
        awkernel_lib::delay::wait_microsec(500);
        phy_auto_timeout(parent, phy)?;
    } else if !ma.flags.contains(MiiFlags::DOINGAUTO) {
        ma.flags |= MiiFlags::DOINGAUTO;
    }

    Ok(JustReturn::Yes)
}

// BMSR_MEDIA_TO_ANAR(x)   (((x) & BMSR_MEDIAMASK) >> 6)
fn bmsr_media_to_anar(x: BMSR) -> u32 {
    let mask = BMSR::ETH_100T4
        | BMSR::ETH_100TXFDX
        | BMSR::ETH_100TXHDX
        | BMSR::ETH_10TFDX
        | BMSR::ETH_10THDX
        | BMSR::ETH_100T2FDX
        | BMSR::ETH_100T2HDX;

    (x.bits() & mask.bits()) >> 6
}

fn phy_auto_timeout(parent: &mut dyn Mii, phy: &mut dyn MiiPhy) -> Result<(), MiiError> {
    let ma = phy.get_attach_args_mut();

    if ma.flags.contains(MiiFlags::DOINGAUTO) {
        ma.flags.remove(MiiFlags::DOINGAUTO);
    } else {
        return Ok(());
    }

    let _bmsr = parent.read_reg(ma.phy_no, MII_BMSR)?;

    // Update the media status.
    phy.service(parent, MiiOpCode::PollStatus)?;

    Ok(())
}

fn mii_media_change(parent: &mut dyn Mii) -> Result<(), MiiError> {
    let mii = parent.get_data_mut();
    let mut tmp = BTreeMap::new();
    core::mem::swap(&mut tmp, &mut mii.phys);

    for (_, phy) in tmp.iter_mut() {
        phy.service(parent, MiiOpCode::MediaChange)?;
    }

    let mii = parent.get_data_mut();
    core::mem::swap(&mut tmp, &mut mii.phys);

    Ok(())
}
