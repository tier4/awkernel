//! Media-independent interface (MII) driver.

pub mod physubr;
pub mod ukphy;

pub const MIIF_RX_DELAY: u32 = 0x00000800; // add RX delay
pub const MIIF_TX_DELAY: u32 = 0x00001000; // add TX delay

// Special `locators' passed to mii_attach().  If one of these is not
// an `any' value, we look for *that* PHY and configure it.  If both
// are not `any', that is an error, and mii_attach() will fail.
pub const MII_OFFSET_ANY: u32 = 0xffffffff;
pub const MII_PHY_ANY: u32 = 0xffffffff;

pub const MII_NPHY: u32 = 32; // max # of PHYs per MII

pub const MII_BMSR: u32 = 0x01; // Basic mode status register (ro)
pub const BMSR_100T4: u32 = 0x8000; // 100 base T4 capable
pub const BMSR_100TXFDX: u32 = 0x4000; // 100 base Tx full duplex capable
pub const BMSR_100TXHDX: u32 = 0x2000; // 100 base Tx half duplex capable
pub const BMSR_10TFDX: u32 = 0x1000; // 10 base T full duplex capable
pub const BMSR_10THDX: u32 = 0x0800; // 10 base T half duplex capable
pub const BMSR_100T2FDX: u32 = 0x0400; // 100 base T2 full duplex capable
pub const BMSR_100T2HDX: u32 = 0x0200; // 100 base T2 half duplex capable
pub const BMSR_EXTSTAT: u32 = 0x0100; // Extended status in register 15
pub const BMSR_MFPS: u32 = 0x0040; // MII Frame Preamble Suppression
pub const BMSR_ACOMP: u32 = 0x0020; // Autonegotiation complete
pub const BMSR_RFAULT: u32 = 0x0010; // Link partner fault
pub const BMSR_ANEG: u32 = 0x0008; // Autonegotiation capable
pub const BMSR_LINK: u32 = 0x0004; // Link status
pub const BMSR_JABBER: u32 = 0x0002; // Jabber detected
pub const BMSR_EXTCAP: u32 = 0x0001; // Extended capability

pub const MII_PHYIDR1: u32 = 0x02; // ID register 1 (ro)

pub const MII_PHYIDR2: u32 = 0x03; // ID register 2 (ro)
pub const IDR2_OUILSB: u32 = 0xfc00; // OUI LSB
pub const IDR2_MODEL: u32 = 0x03f0; // vendor model
pub const IDR2_REV: u32 = 0x000f; // vendor revision

// Note that the EXTSTAT bit indicates that there is extended status
// info available in register 15, but 802.3 section 22.2.4.3 also
// states that all 1000 Mb/s capable PHYs will set this bit to 1.
pub const BMSR_MEDIAMASK: u32 = BMSR_100T4
    | BMSR_100TXFDX
    | BMSR_100TXHDX
    | BMSR_10TFDX
    | BMSR_10THDX
    | BMSR_100T2FDX
    | BMSR_100T2HDX;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MiiError {
    Read,
    Write,
    InvalidParam,
}

pub trait Mii {
    /// Read a register from the PHY.
    fn read_reg(&mut self, phy: u32, reg: u32) -> Result<u32, MiiError>;

    /// Write a register to the PHY.
    fn write_reg(&mut self, phy: u32, reg: u32, data: u32) -> Result<(), MiiError>;
}

#[derive(Debug)]
pub struct MiiData {
    flags: u32,
}

pub trait MiiPhy {
    fn service(&mut self, mii: &mut dyn Mii) -> Result<(), MiiError>;

    fn status(&self, mii: &mut dyn Mii) -> u32;

    fn reset(&mut self, mii: &mut dyn Mii) -> Result<(), MiiError>;

    fn get_args(&self) -> &MiiAttachArgs;

    fn get_args_mut(&mut self) -> &mut MiiAttachArgs;
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

pub fn attach(
    mii: &mut dyn Mii,
    capmask: u32,
    phyloc: u32,
    offloc: u32,
    flags: u32,
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

    let mut mii_data = MiiData { flags: flags };

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
            capmask: capmask,
        };

        ukphy::attach(mii, &mut mii_data, args);
    }

    Ok(())
}
