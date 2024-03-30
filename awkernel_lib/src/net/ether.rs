use crate::net::{
    ip::{IPPROTO_TCP, IPPROTO_UDP},
    ipv6::Ip6Hdr,
    tcp::TCPHdr,
};

use super::{ip::Ip, udp::UDPHdr};

pub const ETHER_CRC_LEN: usize = 4; // Ethernet CRC length
pub const ETHER_MIN_LEN: usize = 64; // Minimum frame length, CRC included
pub const ETHER_MAX_LEN: usize = 1518; // Maximum frame length, CRC included

pub const MAX_JUMBO_FRAME_SIZE: usize = 0x3F00;

pub const ETHER_ADDR_LEN: usize = 6;
pub const ETHER_TYPE_LEN: usize = 2;
pub const ETHER_HDR_LEN: usize = ETHER_ADDR_LEN * 2 + ETHER_TYPE_LEN;

pub const ETHER_TYPE_IP: u16 = 0x0800;
pub const ETHER_TYPE_VLAN: u16 = 0x8100;
pub const ETHER_TYPE_IPV6: u16 = 0x86DD;

pub const ETHER_BROADCAST_ADDR: [u8; ETHER_ADDR_LEN] = [0xff; ETHER_ADDR_LEN];

pub enum NetworkHdr<'a> {
    Ipv4(&'a Ip),
    Ipv6(&'a Ip6Hdr),
    None,
}

pub enum TransportHdr<'a> {
    Udp(&'a UDPHdr),
    Tcp(&'a TCPHdr),
    None,
}

#[derive(Debug, Clone)]
#[repr(C, packed)]
pub struct EtherHeader {
    pub dst: [u8; ETHER_ADDR_LEN],
    pub src: [u8; ETHER_ADDR_LEN],
    pub ether_type: u16,
}

#[derive(Debug, Clone)]
#[repr(C, packed)]
pub struct EtherVlanHeader {
    pub dst: [u8; ETHER_ADDR_LEN],
    pub src: [u8; ETHER_ADDR_LEN],
    pub encap_proto: u16,
    pub vlan_tag: u16,
    pub ether_proto: u16,
}

pub struct EtherExtracted<'a> {
    pub ether: &'a EtherHeader,
    pub ether_vlan: Option<&'a EtherVlanHeader>,
    pub network: NetworkHdr<'a>,
    pub transport: TransportHdr<'a>,
}

pub fn extract_headers(buf: &[u8]) -> Result<EtherExtracted, &'static str> {
    let mut remain = buf.len();

    if core::mem::size_of::<EtherHeader>() > remain {
        return Err("too short ether header");
    }

    let ether = unsafe { &*(buf.as_ptr() as *const EtherHeader) };
    let mut ether_type = u16::from_be(ether.ether_type);

    let ether_vlan = if ether_type == ETHER_TYPE_VLAN {
        if core::mem::size_of::<EtherVlanHeader>() > remain {
            return Ok(EtherExtracted {
                ether,
                ether_vlan: None,
                network: NetworkHdr::None,
                transport: TransportHdr::None,
            });
        }

        remain -= core::mem::size_of::<EtherVlanHeader>();

        let ether_vlan = unsafe { &*(buf.as_ptr() as *const EtherVlanHeader) };
        ether_type = u16::from_be(ether_vlan.ether_proto);

        Some(ether_vlan)
    } else {
        remain -= core::mem::size_of::<EtherHeader>();
        None
    };

    let ipproto;
    let network;

    match ether_type {
        ETHER_TYPE_IP => {
            if core::mem::size_of::<Ip>() > remain {
                return Err("too short ip header");
            }

            let ip = unsafe { &*(buf.as_ptr().add(buf.len() - remain) as *const Ip) };
            let hlen = (ip.header_len() as usize) << 2;

            remain -= hlen;

            ipproto = ip.ip_p;
            network = NetworkHdr::Ipv4(ip);
        }
        ETHER_TYPE_IPV6 => {
            if core::mem::size_of::<Ip6Hdr>() > remain {
                return Err("too short ipv6 header");
            }

            let ip6 = unsafe { &*(buf.as_ptr().add(buf.len() - remain) as *const Ip6Hdr) };
            let hlen = core::mem::size_of::<Ip6Hdr>();

            remain -= hlen;

            ipproto = ip6.next_header;
            network = NetworkHdr::Ipv6(ip6)
        }
        _ => {
            return Ok(EtherExtracted {
                ether,
                ether_vlan,
                network: NetworkHdr::None,
                transport: TransportHdr::None,
            });
        }
    }

    let transport = match ipproto {
        IPPROTO_TCP => {
            if core::mem::size_of::<TCPHdr>() > remain {
                return Err("too short TCP header");
            }

            let tcp = unsafe { &*(buf.as_ptr().add(buf.len() - remain) as *const TCPHdr) };
            TransportHdr::Tcp(tcp)
        }
        IPPROTO_UDP => {
            if core::mem::size_of::<UDPHdr>() > remain {
                return Err("too short UDP header");
            }

            let udp = unsafe { &*(buf.as_ptr().add(buf.len() - remain) as *const UDPHdr) };
            TransportHdr::Udp(udp)
        }
        _ => TransportHdr::None,
    };

    Ok(EtherExtracted {
        ether,
        ether_vlan,
        network,
        transport,
    })
}
