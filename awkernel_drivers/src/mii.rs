//! # Media-independent interface (MII)

use alloc::collections::BTreeMap;
use bitflags::bitflags;

bitflags! {
    #[derive(Debug, Clone, Copy)]
    pub struct MiiFlags: u16 {
        const INITDONE = 0x0001; /* has been initialized (mii_data) */
        const NOISOLATE = 0x0002; /* do not isolate the PHY */
        const NOLOOP = 0x0004; /* no loopback capability */
        const DOINGAUTO = 0x0008; /* doing autonegotiation (mii_softc) */
        const AUTOTSLEEP = 0x0010; /* use tsleep(), not timeout() */
        const HAVEFIBER = 0x0020; /* from parent: has fiber interface */
        const HAVE_GTCR = 0x0040; /* has 100base-T2/1000base-T CR */
        const IS_1000X = 0x0080; /* is a 1000BASE-X device */
        const DOPAUSE = 0x0100; /* advertise PAUSE capability */
        const IS_HPNA = 0x0200; /* is a HomePNA device */
        const FORCEANEG = 0x0400; /* force autonegotiation */
        const SETDELAY = 0x0800; /* set internal delay */
        const RXID = 0x1000; /* add Rx delay */
        const TXID = 0x2000; /* add Tx delay */
        const SGMII = 0x4000; /* MAC to PHY interface is SGMII */
    }
}

pub const MII_BMSR: u32 = 0x01; // Basic mode status register (ro)
pub const MII_PHYIDR1: u32 = 0x02; // ID register 1 (ro)
pub const MII_PHYIDR2: u32 = 0x03; // ID register 2 (ro)

pub const MII_NPHY: u32 = 32; // max # of PHYs per MII

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

#[derive(Debug)]
pub struct MiiData {
    flags: MiiFlags,
    phys: BTreeMap<u32, MiiPhy>,
}

impl MiiData {
    pub fn new(flags: MiiFlags) -> Self {
        Self {
            flags,
            phys: BTreeMap::new(),
        }
    }

    pub fn insert(&mut self, mii_phy: MiiPhy) {
        self.phys.insert(mii_phy.phy_no, mii_phy);
    }
}

#[derive(Debug)]
pub struct MiiPhy {
    phy_no: u32,
    offset: u32,
    id1: u32,
    id2: u32,
    capmask: u32,
}

pub trait Mii {
    fn read(&mut self, phy: u32, reg: u32) -> Option<u32>;
    fn write(&mut self, phy: u32, reg: u32, val: u32);

    fn mii_data(&self) -> &MiiData;
    fn mii_data_mut(&mut self) -> &mut MiiData;
}

#[derive(Debug, Clone, Copy)]
pub enum MiiError {
    ReadError,
    WriteError,
}

pub fn attach(
    mii: &mut impl Mii,
    capmask: u32,
    phyloc: Option<u32>,
    offloc: Option<u32>,
) -> Result<(), MiiError> {
    //     65         struct mii_attach_args ma;
    //     66         struct mii_softc *child;
    //     67         int bmsr, offset = 0;
    //     68         int phymin, phymax;
    //     69
    //     70         if (phyloc != MII_PHY_ANY && offloc != MII_OFFSET_ANY)
    //     71                 panic("mii_attach: phyloc and offloc specified");

    if phyloc.is_some() && offloc.is_some() {
        panic!("mii_attach: phyloc and offloc specified");
    }

    //     72
    //     73         if (phyloc == MII_PHY_ANY) {
    //     74                 phymin = 0;
    //     75                 phymax = MII_NPHY - 1;
    //     76         } else
    //     77                 phymin = phymax = phyloc;
    //     78

    let (phymin, phymax) = if let Some(phyloc) = phyloc {
        (phyloc, phyloc)
    } else {
        (0, MII_NPHY - 1)
    };

    //     79         if ((mii->mii_flags & MIIF_INITDONE) == 0) {
    //     80                 LIST_INIT(&mii->mii_phys);
    //     81                 mii->mii_flags |= MIIF_INITDONE;
    //     82         }

    // if !mii.flags().contains(MiiFlags::INITDONE) {
    //     mii.flags().insert(MiiFlags::INITDONE);
    // }

    //     83
    //     84         for (ma.mii_phyno = phymin; ma.mii_phyno <= phymax; ma.mii_phyno++) {

    let mut offset = 0;
    'outer: for mii_phyno in phymin..=phymax {
        //     85                 /*
        //     86                  * Make sure we haven't already configured a PHY at this
        //     87                  * address.  This allows mii_attach() to be called
        //     88                  * multiple times.
        //     89                  */
        //     90                 for (child = LIST_FIRST(&mii->mii_phys); child != NULL;
        //     91                      child = LIST_NEXT(child, mii_list)) {
        //     92                         if (child->mii_phy == ma.mii_phyno) {
        //     93                                 /*
        //     94                                  * Yes, there is already something
        //     95                                  * configured at this address.
        //     96                                  */
        //     97                                 offset++;
        //     98                                 goto loop_end;
        //     99                         }
        //    100                 }
        //    101

        // Make sure we haven't already configured a PHY at this
        // address.  This allows mii_attach() to be called
        // multiple times.
        for (phy, _) in mii.mii_data().phys.iter() {
            if *phy == mii_phyno {
                // Yes, there is already something
                // configured at this address.
                offset += 1;
                continue 'outer;
            }
        }

        //    102                 /*
        //    103                  * Check to see if there is a PHY at this address.  Note,
        //    104                  * many braindead PHYs report 0/0 in their ID registers,
        //    105                  * so we test for media in the BMSR.
        //    106                  */
        //    107                 bmsr = (*mii->mii_readreg)(parent, ma.mii_phyno, MII_BMSR);
        //    108                 if (bmsr == 0 || bmsr == 0xffff ||
        //    109                     (bmsr & (BMSR_MEDIAMASK|BMSR_EXTSTAT)) == 0) {
        //    110                         /* Assume no PHY at this address. */
        //    111                         goto loop_end;
        //    112                 }
        //    113

        let bmsr = mii.read(mii_phyno, MII_BMSR).ok_or(MiiError::ReadError)?;
        if bmsr == 0 || bmsr == 0xffff || (bmsr & (BMSR_MEDIAMASK | BMSR_EXTSTAT)) == 0 {
            // Assume no PHY at this address.
            continue 'outer;
        }

        //    114                 /*
        //    115                  * There is a PHY at this address.  If we were given an
        //    116                  * `offset' locator, skip this PHY if it doesn't match.
        //    117                  */
        //    118                 if (offloc != MII_OFFSET_ANY && offloc != offset) {
        //    119                         offset++;
        //    120                         goto loop_end;
        //    121                 }

        // There is a PHY at this address.  If we were given an
        // `offset' locator, skip this PHY if it doesn't match.
        if let Some(offloc) = offloc {
            if offloc != offset {
                offset += 1;
                continue 'outer;
            }
        }

        //    122
        //    123                 /*
        //    124                  * Extract the IDs.  Braindead PHYs will be handled by
        //    125                  * the `ukphy' driver, as we have no ID information to
        //    126                  * match on.
        //    127                  */
        //    128                 ma.mii_id1 = (*mii->mii_readreg)(parent, ma.mii_phyno,
        //    129                     MII_PHYIDR1);
        //    130                 ma.mii_id2 = (*mii->mii_readreg)(parent, ma.mii_phyno,
        //    131                     MII_PHYIDR2);

        // Extract the IDs.  Braindead PHYs will be handled by
        // the `ukphy' driver, as we have no ID information to
        // match on.
        let id1 = mii
            .read(mii_phyno, MII_PHYIDR1)
            .ok_or(MiiError::ReadError)?;
        let id2 = mii
            .read(mii_phyno, MII_PHYIDR2)
            .ok_or(MiiError::ReadError)?;

        log::debug!("MII: id1: {:#x}", id1);
        log::debug!("MII: id2: {:#x}", id2);

        mii.mii_data_mut().insert(MiiPhy {
            phy_no: mii_phyno,
            offset,
            id1,
            id2,
            capmask,
        });
    }

    Ok(())
}
