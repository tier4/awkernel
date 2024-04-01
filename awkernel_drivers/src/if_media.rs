use alloc::vec::Vec;

pub const IFM_ETHER: u64 = 0x0000000000000100;
pub const IFM_10_T: u64 = 3; // 10BaseT - RJ45
pub const IFM_10_2: u64 = 4; // 10Base2 - Thinnet
pub const IFM_10_5: u64 = 5; // 10Base5 - AUI
pub const IFM_100_TX: u64 = 6; // 100BaseTX - RJ45
pub const IFM_100_FX: u64 = 7; // 100BaseFX - Fiber
pub const IFM_100_T4: u64 = 8; // 100BaseT4 - 4 pair cat 3
pub const IFM_100_VG: u64 = 9; // 100VG-AnyLAN
pub const IFM_100_T2: u64 = 10; // 100BaseT2
pub const IFM_1000_SX: u64 = 11; // 1000BaseSX - multi-mode fiber
pub const IFM_10_STP: u64 = 12; // 10BaseT over shielded TP
pub const IFM_10_FL: u64 = 13; // 10BaseFL - Fiber
pub const IFM_1000_LX: u64 = 14; // 1000baseLX - single-mode fiber
pub const IFM_1000_CX: u64 = 15; // 1000baseCX - 150ohm STP
pub const IFM_1000_T: u64 = 16; // 1000baseT - 4 pair cat 5
pub const IFM_1000_TX: u64 = IFM_1000_T; // for backwards compatibility
pub const IFM_HPNA_1: u64 = 17; // HomePNA 1.0 (1Mb/s)
pub const IFM_10G_LR: u64 = 18; // 10GBase-LR - single-mode fiber
pub const IFM_10G_SR: u64 = 19; // 10GBase-SR - multi-mode fiber
pub const IFM_10G_CX4: u64 = 20; // 10GBase-CX4 - copper
pub const IFM_2500_SX: u64 = 21; // 2500baseSX - multi-mode fiber
pub const IFM_10G_T: u64 = 22; // 10GbaseT cat 6
pub const IFM_10G_SFP_CU: u64 = 23; // 10G SFP+ direct attached cable
pub const IFM_10G_LRM: u64 = 24; // 10GBase-LRM 850nm Multi-mode
pub const IFM_40G_CR4: u64 = 25; // 40GBase-CR4
pub const IFM_40G_SR4: u64 = 26; // 40GBase-SR4
pub const IFM_40G_LR4: u64 = 27; // 40GBase-LR4
pub const IFM_1000_KX: u64 = 28; // 1000Base-KX backplane
pub const IFM_10G_KX4: u64 = 29; // 10GBase-KX4 backplane
pub const IFM_10G_KR: u64 = 30; // 10GBase-KR backplane
pub const IFM_10G_CR1: u64 = 31; // 10GBase-CR1 Twinax splitter
pub const IFM_20G_KR2: u64 = 32; // 20GBase-KR2 backplane
pub const IFM_2500_KX: u64 = 33; // 2500Base-KX backplane
pub const IFM_2500_T: u64 = 34; // 2500Base-T - RJ45 (NBaseT)
pub const IFM_5000_T: u64 = 35; // 5000Base-T - RJ45 (NBaseT)
pub const IFM_1000_SGMII: u64 = 36; // 1G media interface
pub const IFM_10G_SFI: u64 = 37; // 10G media interface
pub const IFM_40G_XLPPI: u64 = 38; // 40G media interface
pub const IFM_1000_CX_SGMII: u64 = 39; // 1000Base-CX-SGMII
pub const IFM_40G_KR4: u64 = 40; // 40GBase-KR4
pub const IFM_10G_ER: u64 = 41; // 10GBase-ER
pub const IFM_100G_CR4: u64 = 42; // 100GBase-CR4
pub const IFM_100G_SR4: u64 = 43; // 100GBase-SR4
pub const IFM_100G_KR4: u64 = 44; // 100GBase-KR4
pub const IFM_100G_LR4: u64 = 45; // 100GBase-LR4
pub const IFM_56G_R4: u64 = 46; // 56GBase-R4
pub const IFM_25G_CR: u64 = 47; // 25GBase-CR
pub const IFM_25G_KR: u64 = 48; // 25GBase-KR
pub const IFM_25G_SR: u64 = 49; // 25GBase-SR
pub const IFM_50G_CR2: u64 = 50; // 50GBase-CR2
pub const IFM_50G_KR2: u64 = 51; // 50GBase-KR2
pub const IFM_25G_LR: u64 = 52; // 25GBase-LR
pub const IFM_25G_ER: u64 = 53; // 25GBase-ER
pub const IFM_10G_AOC: u64 = 54; // 10G Active Optical Cable
pub const IFM_25G_AOC: u64 = 55; // 25G Active Optical Cable
pub const IFM_40G_AOC: u64 = 56; // 40G Active Optical Cable
pub const IFM_100G_AOC: u64 = 57; // 100G Active Optical Cable

pub const IFM_AVALID: u64 = 0x0000000000000001; // Active bit valid
pub const IFM_ACTIVE: u64 = 0x0000000000000002; // Interface attached to working net

// Shared media sub-types
pub const IFM_AUTO: u64 = 0; // Autoselect best media
pub const IFM_MANUAL: u64 = 1; // Jumper/dipswitch selects media
pub const IFM_NONE: u64 = 2; // Deselect all media

// Shared options
pub const IFM_FDX: u64 = 0x0000010000000000; // Force full duplex
pub const IFM_HDX: u64 = 0x0000020000000000; // Force half duplex
pub const IFM_FLOW: u64 = 0x0000040000000000; // enable hardware flow control
pub const IFM_FLAG0: u64 = 0x0000100000000000; // Driver defined flag
pub const IFM_FLAG1: u64 = 0x0000200000000000; // Driver defined flag
pub const IFM_FLAG2: u64 = 0x0000400000000000; // Driver defined flag
pub const IFM_LOOP: u64 = 0x0000800000000000; // Put hardware in loopback

pub const IFM_ETH_MASTER: u64 = 0x0000000000010000; // master mode (1000baseT)
pub const IFM_ETH_RXPAUSE: u64 = 0x0000000000020000; // receive PAUSE frames
pub const IFM_ETH_TXPAUSE: u64 = 0x0000000000040000; // transmit PAUSE frames

pub const IFM_TMASK: u64 = 0x00000000000000ff; // Media sub-type
pub const IFM_IMASK: u64 = 0xff00000000000000; // Instance mask
pub const IFM_ISHIFT: u64 = 56; // Instance shift

#[inline(always)]
pub fn ifm_subtype(media: &Media) -> u64 {
    media.0 & IFM_TMASK
}

/// Create a media word.
#[inline(always)]
pub fn ifm_make_word(r#type: u64, subtype: u64, options: u64, instance: u64) -> Media {
    Media(r#type | subtype | options | (instance << IFM_ISHIFT))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Media(u64);

impl Media {
    #[inline(always)]
    pub const fn new(value: u64) -> Self {
        Self(value)
    }

    #[inline(always)]
    pub fn get_value(&self) -> u64 {
        self.0
    }

    #[inline(always)]
    pub fn insert(&mut self, value: u64) {
        self.0 |= value;
    }

    #[inline(always)]
    pub fn contains(&self, value: u64) -> bool {
        self.0 & value != 0
    }

    pub fn link_speed(&self) -> u64 {
        let subtype = ifm_subtype(self);

        match subtype {
            IFM_100G_AOC | IFM_100G_LR4 | IFM_100G_SR4 | IFM_100G_CR4 | IFM_100G_KR4 => 100_000,
            IFM_56G_R4 => 56_000,
            IFM_40G_AOC | IFM_40G_LR4 | IFM_40G_SR4 | IFM_40G_CR4 | IFM_40G_KR4 | IFM_40G_XLPPI => {
                40_000
            }
            IFM_25G_AOC | IFM_25G_LR | IFM_25G_ER | IFM_25G_SR | IFM_25G_KR | IFM_25G_CR => 25_000,
            IFM_10G_AOC | IFM_10G_ER | IFM_10G_LR | IFM_10G_LRM | IFM_10G_SR | IFM_10G_CR1
            | IFM_10G_KR | IFM_10G_KX4 | IFM_10G_SFI | IFM_10G_T | IFM_10G_CX4 | IFM_10G_SFP_CU => {
                10_000
            }
            IFM_5000_T => 5_000,
            IFM_2500_KX | IFM_2500_T | IFM_2500_SX => 2_500,
            IFM_1000_T | IFM_1000_SGMII | IFM_1000_CX | IFM_1000_CX_SGMII | IFM_1000_SX
            | IFM_1000_LX | IFM_1000_KX => 1_000,
            IFM_100_TX | IFM_100_FX | IFM_100_T2 | IFM_100_VG | IFM_100_T4 => 100,
            IFM_10_T | IFM_10_STP | IFM_10_FL | IFM_10_2 | IFM_10_5 => 10,
            IFM_HPNA_1 => 1,
            _ => 0,
        }
    }
}

#[derive(Debug)]
pub struct Ifmedia {
    ifm_mask: u64,                 // mask of changes we don't care about
    ifm_media: Media,              // current user-set media word
    ifm_cur: Option<IfmediaEntry>, // [M] currently selected media
    ifm_list: Vec<IfmediaEntry>,   // [M] list of all supported media
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfmediaEntry {
    pub media: Media, // description of this media attachment
    pub data: u32,    // for driver-specific use
}

impl IfmediaEntry {
    #[inline(always)]
    pub fn get_instance(&self) -> u32 {
        ((self.media.0 >> IFM_ISHIFT) & 0xff) as u32
    }
}

impl Ifmedia {
    pub fn new(ifm_mask: u64, ifm_media: Media) -> Self {
        Self {
            ifm_mask,
            ifm_media,
            ifm_cur: None,
            ifm_list: Vec::new(),
        }
    }

    #[inline(always)]
    pub fn add(&mut self, media: IfmediaEntry) {
        self.ifm_list.push(media);
    }

    #[inline(always)]
    pub fn set_mask(&mut self, mask: u64) {
        self.ifm_mask |= mask;
    }

    /// Find the media with the most bits in common with the target,
    /// and set it as the current media.
    ///
    /// If no media is found, return false.
    #[inline(always)]
    pub fn set_current_media(&mut self, target: u64) -> bool {
        self.ifm_cur = self.find(target).cloned();
        self.ifm_cur.is_some()
    }

    /// Find the media with the most bits in common with the target.
    /// If no media is found, return None.
    /// If multiple media are found, return the last one.
    pub fn find(&self, target: u64) -> Option<&IfmediaEntry> {
        let mask = !self.ifm_mask;
        self.ifm_list
            .iter()
            .find(|&m| m.media.0 & mask == target & mask)
    }

    #[inline(always)]
    pub fn get_current(&self) -> Option<&IfmediaEntry> {
        self.ifm_cur.as_ref()
    }

    #[inline(always)]
    pub fn get_media(&self) -> &Media {
        &self.ifm_media
    }
}

#[inline(always)]
pub fn is_media_active(media: Media) -> bool {
    media.0 & IFM_ACTIVE != 0
}

#[inline(always)]
pub fn is_full_duplex(media: Media) -> bool {
    media.0 & IFM_FDX != 0
}
