use alloc::vec::Vec;
use bitflags::bitflags;
use core::net::Ipv4Addr;

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct PacketHeaderFlags: u16 {
        const IPV4_CSUM_OUT = 0x0001; // IPv4 checksum needed
        const TCP_CSUM_OUT = 0x0002; // TCP checksum needed
        const UDP_CSUM_OUT = 0x0004; // UDP checksum needed
        const IPV4_CSUM_IN_OK = 0x0008; // IPv4 checksum verified
        const IPV4_CSUM_IN_BAD = 0x0010; // IPv4 checksum bad
        const TCP_CSUM_IN_OK = 0x0020; // TCP checksum verified
        const TCP_CSUM_IN_BAD = 0x0040; // TCP checksum bad
        const UDP_CSUM_IN_OK = 0x0080; // UDP checksum verified
        const UDP_CSUM_IN_BAD = 0x0100; // UDP checksum bad
        const ICMP_CSUM_OUT = 0x0200; // ICMP/ICMPv6 checksum needed
        const ICMP_CSUM_IN_OK = 0x0400; // ICMP/ICMPv6 checksum verified
        const ICMP_CSUM_IN_BAD = 0x0800; // ICMP/ICMPv6 checksum bad
        const IPV6_DF_OUT = 0x1000; // don't fragment outgoing IPv6
        const TIMESTAMP = 0x2000; // ph_timestamp is set
        const FLOWID = 0x4000; // ph_flowid is set
        const TCP_TSO = 0x8000; // TCP Segmentation Offload needed
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct NetFlags: u16 {
        const UP = 1 << 0; // interface is up
        const BROADCAST = 1 << 1; // broadcast address valid
        const DEBUG = 1 << 2; // turn on debugging
        const LOOPBACK = 1 << 3; // is a loopback net
        const POINTOPOINT = 1 << 4; // is point-to-point link
        const STATICARP = 1 << 5; // only static ARP
        const RUNNING = 1 << 6; // resources allocated
        const NOARP = 1 << 7; // no address resolution protocol
        const PROMISC = 1 << 8; // receive all packets
        const ALLMULTI = 1 << 9; // receive all multicast packets
        const OACTIVE = 1 << 10; // transmission in progress
        const SIMPLEX = 1 << 11; // can't hear own transmissions
        const LINK0 = 1 << 12; // per link layer defined bit
        const LINK1 = 1 << 13; // per link layer defined bit
        const LINK2 = 1 << 14; // per link layer defined bit
        const MULTICAST = 1 << 15; // supports multicast
    }

    /// Capabilities that interfaces can advertise.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct NetCapabilities: u32 {
        const CSUM_IPv4 = 1 << 0; // can do IPv4 header csum
        const CSUM_TCPv4 = 1 << 1; // can do IPv4/TCP csum
        const CSUM_UDPv4 = 1 << 2; // can do IPv4/UDP csum
        const VLAN_MTU = 1 << 4; // VLAN-compatible MTU
        const VLAN_HWTAGGING = 1 << 5; // hardware VLAN tag support
        const CSUM_TCPv6 = 1 << 7; // can do IPv6/TCP checksums
        const CSUM_UDPv6 = 1 << 8; // can do IPv6/UDP checksums
        const TSOv4 = 1 << 12; // IPv4/TCP segment offload
        const TSOv6 = 1 << 13; // IPv6/TCP segment offload
        const LRO = 1 << 14; // TCP large recv offload
        const WOL = 1 << 15; // can do wake on lan
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NetDevError {
    AlreadyUp,
    AlreadyDown,
    DeviceError,
    MulticastAddrError,
}

#[derive(Debug, Clone)]
pub struct EtherFrameRef<'a> {
    pub data: &'a [u8],
    pub vlan: Option<u16>,
    pub csum_flags: PacketHeaderFlags,
}

#[derive(Debug, Clone)]
pub struct EtherFrameBuf {
    pub data: Vec<u8>,
    pub vlan: Option<u16>,
}

/// Because the network will have multiple queues
/// and the queues will be processed in parallel,
/// the network device must be thread-safe.
pub trait NetDevice {
    fn recv(&self, que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError>;
    fn send(&self, data: EtherFrameRef, que_id: usize) -> Result<(), NetDevError>;

    fn flags(&self) -> NetFlags;
    fn capabilities(&self) -> NetCapabilities;

    /// Link speed in Mbps.
    fn link_speed(&self) -> u64;

    fn can_send(&self) -> bool;
    fn mac_address(&self) -> [u8; 6];
    fn link_up(&self) -> bool;
    fn full_duplex(&self) -> bool;

    fn device_short_name(&self) -> &'static str;

    fn up(&self) -> Result<(), NetDevError>;
    fn down(&self) -> Result<(), NetDevError>;

    /// Update network device status.
    fn update(&self) -> Result<(), NetDevError>;

    /// Interrupt handler for network device.
    fn interrupt(&self, irq: u16) -> Result<(), NetDevError>;
    fn irqs(&self) -> Vec<u16>;
    fn rx_irq_to_que_id(&self, irq: u16) -> usize;

    fn add_multicast_addr_ipv4(&self, addr: Ipv4Addr) -> Result<(), NetDevError>;
    fn add_multicast_range_ipv4(&self, start: Ipv4Addr, end: Ipv4Addr) -> Result<(), NetDevError>;

    fn remove_multicast_addr_ipv4(&self, addr: Ipv4Addr) -> Result<(), NetDevError>;
    fn remove_multicast_range_ipv4(
        &self,
        start: Ipv4Addr,
        end: Ipv4Addr,
    ) -> Result<(), NetDevError>;
}
