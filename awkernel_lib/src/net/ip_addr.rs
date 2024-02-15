use core::net::{Ipv4Addr, Ipv6Addr};

/// Wrapper for `smoltcp::wire::IpAddress` to convert to and from `core::net::IpAddr`.
#[derive(Debug, Clone)]
pub struct IpAddr {
    pub(super) addr: smoltcp::wire::IpAddress,
}

impl IpAddr {
    pub fn new_v4(addr: Ipv4Addr) -> IpAddr {
        let octets = addr.octets();
        IpAddr {
            addr: smoltcp::wire::IpAddress::Ipv4(smoltcp::wire::Ipv4Address::new(
                octets[0], octets[1], octets[2], octets[3],
            )),
        }
    }

    pub fn new_v6(addr: Ipv6Addr) -> IpAddr {
        let octets = addr.octets();
        IpAddr {
            addr: smoltcp::wire::IpAddress::Ipv6(smoltcp::wire::Ipv6Address::new(
                ((octets[0] as u16) << 8) | octets[1] as u16,
                ((octets[2] as u16) << 8) | octets[3] as u16,
                ((octets[4] as u16) << 8) | octets[5] as u16,
                ((octets[6] as u16) << 8) | octets[7] as u16,
                ((octets[8] as u16) << 8) | octets[9] as u16,
                ((octets[10] as u16) << 8) | octets[11] as u16,
                ((octets[12] as u16) << 8) | octets[13] as u16,
                ((octets[14] as u16) << 8) | octets[15] as u16,
            )),
        }
    }

    pub fn get_addr(&self) -> core::net::IpAddr {
        match self.addr {
            smoltcp::wire::IpAddress::Ipv4(addr) => core::net::IpAddr::V4(
                core::net::Ipv4Addr::new(addr.0[0], addr.0[1], addr.0[2], addr.0[3]),
            ),
            smoltcp::wire::IpAddress::Ipv6(addr) => {
                core::net::IpAddr::V6(core::net::Ipv6Addr::new(
                    ((addr.0[1] as u16) << 8) | addr.0[0] as u16,
                    ((addr.0[3] as u16) << 8) | addr.0[2] as u16,
                    ((addr.0[5] as u16) << 8) | addr.0[4] as u16,
                    ((addr.0[7] as u16) << 8) | addr.0[6] as u16,
                    ((addr.0[9] as u16) << 8) | addr.0[8] as u16,
                    ((addr.0[11] as u16) << 8) | addr.0[10] as u16,
                    ((addr.0[13] as u16) << 8) | addr.0[12] as u16,
                    ((addr.0[15] as u16) << 8) | addr.0[14] as u16,
                ))
            }
        }
    }

    #[inline(always)]
    pub fn is_ipv4(&self) -> bool {
        match self.addr {
            smoltcp::wire::IpAddress::Ipv4(_) => true,
            smoltcp::wire::IpAddress::Ipv6(_) => false,
        }
    }

    #[inline(always)]
    pub fn is_ipv6(&self) -> bool {
        match self.addr {
            smoltcp::wire::IpAddress::Ipv4(_) => false,
            smoltcp::wire::IpAddress::Ipv6(_) => true,
        }
    }
}
