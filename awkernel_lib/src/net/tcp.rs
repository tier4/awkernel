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

/// Create a TCP socket.
#[cfg(feature = "std")]
pub(super) fn create_socket(
    addr: &crate::net::ip_addr::IpAddr,
    port: u16,
) -> Result<(socket2::Socket, socket2::SockAddr), super::NetManagerError> {
    // Create a socket address.

    use super::NetManagerError;

    let ip = addr.get_addr();
    let socket_addr = core::net::SocketAddr::new(ip, port);
    let sock_addr = socket2::SockAddr::from(socket_addr);

    let domain = if socket_addr.is_ipv4() {
        socket2::Domain::IPV4
    } else if sock_addr.is_ipv6() {
        socket2::Domain::IPV6
    } else {
        return Err(NetManagerError::InvalidSocketAddress);
    };

    // Create a socket.
    let socket = socket2::Socket::new(domain, socket2::Type::STREAM, Some(socket2::Protocol::TCP))
        .or(Err(NetManagerError::SocketError))?;

    Ok((socket, sock_addr))
}
