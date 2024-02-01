#[repr(C, packed)]
pub struct Ip6Hdr {
    ver_tc_fl: [u8; 4],
    pub payload_len: u16,
    pub next_header: u8,
    pub hop_limit: u8,
    pub src: [u8; 16],
    pub dst: [u8; 16],
}

impl Ip6Hdr {
    #[inline]
    pub fn version(&self) -> u8 {
        self.ver_tc_fl[0] >> 4
    }

    #[inline]
    pub fn traffic_class(&self) -> u8 {
        (self.ver_tc_fl[0] & 0xf) << 4 | self.ver_tc_fl[1] >> 4
    }

    #[inline]
    pub fn flow_label(&self) -> u32 {
        ((self.ver_tc_fl[1] & 0xf) as u32) << 16
            | (self.ver_tc_fl[2] as u32) << 8
            | self.ver_tc_fl[3] as u32
    }
}
