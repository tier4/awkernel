//! # Media-independent interface (MII)

use bitflags::bitflags;

bitflags! {
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
