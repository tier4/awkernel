#[derive(Debug, Clone)]
#[repr(C, packed)]
pub struct TCPHdr {
    pub th_sport: u16, // source port
    pub th_dport: u16, // destination port
    pub th_seq: u32,   // sequence number
    pub th_ack: u32,   // acknowledgement number
    th_x2_off: u8,     // (unused) and data offset
    pub th_flags: u8,
    pub th_win: u16, // window
    pub th_sum: u16, // checksum
    pub th_urp: u16, // urgent pointer
}

impl TCPHdr {
    #[inline]
    pub fn data_offset(&self) -> u8 {
        self.th_x2_off >> 4
    }
}
