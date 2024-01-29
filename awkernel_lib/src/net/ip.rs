pub const IPPROTO_TCP: u8 = 6; // tcp
pub const IPPROTO_UDP: u8 = 17; // udp

#[derive(Debug, Clone)]
#[repr(C, packed)]
pub struct Ip {
    ip_ver_len: u8,  // version and header length
    pub ip_tos: u8,  // type of service
    pub ip_len: u16, // total length
    pub ip_id: u16,  // identification
    pub ip_off: u16, // fragment offset field
    pub ip_ttl: u8,  // time to live
    pub ip_p: u8,    // protocol
    pub ip_sum: u16, // checksum
    pub ip_src: u32, // source address
    pub ip_dst: u32, // dest address
}

impl Ip {
    #[inline]
    pub fn version(&self) -> u8 {
        self.ip_ver_len >> 4
    }

    #[inline]
    pub fn header_len(&self) -> u8 {
        self.ip_ver_len & 0xf
    }
}
