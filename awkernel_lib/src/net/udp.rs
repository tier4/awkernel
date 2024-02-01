#[derive(Debug, Clone)]
#[repr(C, packed)]
pub struct UDPHdr {
    pub uh_sport: u16, // source port
    pub uh_dport: u16, // destination port
    pub uh_ulen: u16,  // udp length
    pub uh_sum: u16,   // udp checksum
}
