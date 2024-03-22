//! # Media-independent interface (MII)

use alloc::collections::BTreeMap;
use bitflags::bitflags;

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

pub const MII_BMSR: u32 = 0x01; // Basic mode status register (ro)
pub const MII_PHYIDR1: u32 = 0x02; // ID register 1 (ro)
pub const MII_PHYIDR2: u32 = 0x03; // ID register 2 (ro)

pub const MII_ANAR: u32 = 0x04; // Autonegotiation advertisement (rw)

pub const MII_ANLPAR: u32 = 0x05; // Autonegotiation lnk partner abilities (rw)
pub const ANLPAR_T4: u32 = 0x0200; // link partner supports 100bT4
pub const ANLPAR_TX_FD: u32 = 0x0100; // link partner supports 100bTx FD
pub const ANLPAR_TX: u32 = 0x0080; // link partner supports 100bTx
pub const ANLPAR_10_FD: u32 = 0x0040; // link partner supports 10bT FD
pub const ANLPAR_10: u32 = 0x0020; // link partner supports 10bT

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

pub const BMSR_100T4: u32 = 0x8000; // 100 base T4 capable
pub const BMSR_100TXFDX: u32 = 0x4000; // 100 base Tx full duplex capable
pub const BMSR_100TXHDX: u32 = 0x2000; // 100 base Tx half duplex capable
pub const BMSR_10TFDX: u32 = 0x1000; // 10 base T full duplex capable
pub const BMSR_10THDX: u32 = 0x0800; // 10 base T half duplex capable
pub const BMSR_MFPS: u32 = 0x0040; // MII Frame Preamble Suppression
pub const BMSR_100T2FDX: u32 = 0x0400; // 100 base T2 full duplex capable
pub const BMSR_100T2HDX: u32 = 0x0200; // 100 base T2 half duplex capable
pub const BMSR_EXTSTAT: u32 = 0x0100; // Extended status in register 15
pub const BMSR_ACOMP: u32 = 0x0020; // Autonegotiation complete
pub const BMSR_RFAULT: u32 = 0x0010; // Link partner fault
pub const BMSR_ANEG: u32 = 0x0008; // Autonegotiation capable
pub const BMSR_LINK: u32 = 0x0004; // Link status
pub const BMSR_JABBER: u32 = 0x0002; // Jabber detected
pub const BMSR_EXTCAP: u32 = 0x0001; // Extended capability

pub const BMSR_MEDIAMASK: u32 = BMSR_100T4
    | BMSR_100TXFDX
    | BMSR_100TXHDX
    | BMSR_10TFDX
    | BMSR_10THDX
    | BMSR_100T2FDX
    | BMSR_100T2HDX;

pub const MII_EXTSR: u32 = 0x0f; // Extended status register
pub const EXTSR_1000XFDX: u32 = 0x8000; // 1000X full-duplex capable
pub const EXTSR_1000XHDX: u32 = 0x4000; // 1000X half-duplex capable
pub const EXTSR_1000TFDX: u32 = 0x2000; // 1000T full-duplex capable
pub const EXTSR_1000THDX: u32 = 0x1000; // 1000T half-duplex capable

#[derive(Debug)]
pub struct MiiData {
    flags: MiiFlags,
    phys: BTreeMap<u32, MiiAttachArgs>,
    current_media: Option<u64>,

    media_active: u64,
    media_status: u64,
}

impl MiiData {
    pub fn new(flags: MiiFlags) -> Self {
        Self {
            flags,
            phys: BTreeMap::new(),
            current_media: None,
            media_active: 0,
            media_status: 0,
        }
    }

    pub fn insert(&mut self, mii_phy: MiiAttachArgs) {
        self.phys.insert(mii_phy.phy_no, mii_phy);
    }
}

#[derive(Debug)]
pub struct MiiAttachArgs {
    phy_no: u32,           // MII address
    id1: u32,              // PHY ID register 1
    id2: u32,              // PHY ID register 2
    capmask: u32,          // capability mask from BMSR
    flags: MiiFlags,       // flags from parent.
    ext_capabilities: u32, // extended capabilities

    media_active: u64,
    media_status: u64,
}

pub trait Mii {
    fn read_reg(&mut self, phy: u32, reg: u32) -> Option<u32>;
    fn write_reg(&mut self, phy: u32, reg: u32, val: u32);

    fn get_data(&self) -> &MiiData;
    fn get_data_mut(&mut self) -> &mut MiiData;
}

pub trait MiiPhy {
    /// # The Service routine of the PHY.
    ///
    /// `parent` is the parent device.
    /// `ma` is the PHY's attach args.
    fn service(&self, parent: &mut dyn Mii, ma: &mut MiiAttachArgs, opcode: MiiOpCode);

    /// `parent` is the parent device.
    fn status(&self, parent: &mut dyn Mii, ma: &mut MiiAttachArgs) -> Result<(), MiiError>;

    /// `parent` is the parent device.
    fn reset(&self, parent: &mut dyn Mii);
}

#[derive(Debug, Clone, Copy)]
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
}

pub fn attach(
    mii: &mut impl Mii,
    mii_data: &mut MiiData,
    capmask: u32,
    phyloc: Option<u32>,
    offloc: Option<u32>,
) -> Result<(), MiiError> {
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
        for (phy, _) in mii_data.phys.iter() {
            if *phy == mii_phyno {
                // Yes, there is already something
                // configured at this address.
                offset += 1;
                continue 'outer;
            }
        }

        let bmsr = mii
            .read_reg(mii_phyno, MII_BMSR)
            .ok_or(MiiError::ReadError)?;
        if bmsr == 0 || bmsr == 0xffff || (bmsr & (BMSR_MEDIAMASK | BMSR_EXTSTAT)) == 0 {
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
        let id1 = mii
            .read_reg(mii_phyno, MII_PHYIDR1)
            .ok_or(MiiError::ReadError)?;
        let id2 = mii
            .read_reg(mii_phyno, MII_PHYIDR2)
            .ok_or(MiiError::ReadError)?;

        log::debug!("MII: id1: {:#x}", id1);
        log::debug!("MII: id2: {:#x}", id2);

        let ma = MiiAttachArgs {
            phy_no: mii_phyno,
            id1,
            id2,
            capmask,
            flags: mii_data.flags,
            media_active: 0,
            media_status: 0,
            ext_capabilities: 0,
        };

        mii_data.phys.insert(mii_phyno, ma);
    }

    Ok(())
}

/// Inform the PHYs that the interface is down.
pub fn down(dev: &mut dyn Mii, mii_data: &mut MiiData, phy: &mut dyn MiiPhy) {
    for (_, ma) in mii_data.phys.iter_mut() {
        phy.service(dev, ma, MiiOpCode::Down);
    }
}

fn phy_down(ma: &mut MiiAttachArgs) {
    if ma.flags.contains(MiiFlags::DOINGAUTO) {
        ma.flags.remove(MiiFlags::DOINGAUTO);
        // timeout_del(&sc->mii_phy_timo);
    }
}

fn phy_status(parent: &mut dyn Mii, ma: &mut MiiAttachArgs, phy: &dyn MiiPhy) {
    phy.status(parent, ma);
}
