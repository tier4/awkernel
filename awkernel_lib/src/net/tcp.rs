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

#[allow(dead_code)]
#[derive(Debug)]
pub struct TcpPort {
    port: u16,
    is_ipv4: bool,
}

impl TcpPort {
    pub fn new(port: u16, is_ipv4: bool) -> Self {
        Self { port, is_ipv4 }
    }

    #[inline(always)]
    pub fn port(&self) -> u16 {
        self.port
    }
}

impl Drop for TcpPort {
    fn drop(&mut self) {
        #[cfg(not(feature = "std"))]
        {
            let mut net_manager = super::NET_MANAGER.write();
            if self.is_ipv4 {
                net_manager.decrement_port_in_use_tcp_ipv4(self.port);
            } else {
                net_manager.decrement_port_in_use_tcp_ipv6(self.port);
            }
        }
    }
}
