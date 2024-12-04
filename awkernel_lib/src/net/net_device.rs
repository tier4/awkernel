use crate::{
    dma_pool::DMAPool,
    paging::PAGESIZE,
    sync::{mcs::MCSNode, mutex::Mutex},
};
use alloc::borrow::Cow;
use bitflags::bitflags;
use core::fmt::Display;

#[cfg(not(feature = "std"))]
use alloc::{string::String, vec::Vec};

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
pub enum LinkStatus {
    Up,
    UpFullDuplex,
    UpHalfDuplex,
    Down,
    Unknown,
}

impl Display for NetCapabilities {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut s = String::new();

        if self.contains(NetCapabilities::CSUM_IPv4) {
            s.push_str("CSUM_IPv4 ");
        }

        if self.contains(NetCapabilities::CSUM_TCPv4) {
            s.push_str("CSUM_TCPv4 ");
        }

        if self.contains(NetCapabilities::CSUM_UDPv4) {
            s.push_str("CSUM_UDPv4 ");
        }

        if self.contains(NetCapabilities::VLAN_MTU) {
            s.push_str("VLAN_MTU ");
        }

        if self.contains(NetCapabilities::VLAN_HWTAGGING) {
            s.push_str("VLAN_HWTAGGING ");
        }

        if self.contains(NetCapabilities::CSUM_TCPv6) {
            s.push_str("CSUM_TCPv6 ");
        }

        if self.contains(NetCapabilities::CSUM_UDPv6) {
            s.push_str("CSUM_UDPv6 ");
        }

        if self.contains(NetCapabilities::TSOv4) {
            s.push_str("TSOv4 ");
        }

        if self.contains(NetCapabilities::TSOv6) {
            s.push_str("TSOv6 ");
        }

        if self.contains(NetCapabilities::LRO) {
            s.push_str("LRO ");
        }

        if self.contains(NetCapabilities::WOL) {
            s.push_str("WOL ");
        }

        write!(f, "{}", s)
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

#[derive(Debug)]
pub struct EtherFrameDMA {
    pub data: DMAPool<[u8; PAGESIZE]>,
    pub vlan: Option<u16>,
}

#[derive(Debug)]
pub struct EtherFrameDMAcsum {
    pub data: DMAPool<[u8; PAGESIZE]>,
    pub len: usize,
    pub vlan: Option<u16>,
    pub csum_flags: PacketHeaderFlags,
}

/// Because the network will have multiple queues
/// and the queues will be processed in parallel,
/// the network device must be thread-safe.
pub trait NetDevice {
    fn recv(&self, que_id: usize) -> Result<Option<EtherFrameDMA>, NetDevError>;
    fn send(&self, que_id: usize) -> Result<(), NetDevError>;
    fn push(&self, data: EtherFrameDMAcsum, que_id: usize) -> Result<(), NetDevError>;

    fn flags(&self) -> NetFlags;
    fn capabilities(&self) -> NetCapabilities;

    /// Link speed in Mbps.
    fn link_speed(&self) -> u64;

    fn can_send(&self) -> bool;
    fn mac_address(&self) -> [u8; 6];

    fn link_status(&self) -> LinkStatus;

    fn device_short_name(&self) -> Cow<'static, str>;

    fn up(&self) -> Result<(), NetDevError>;
    fn down(&self) -> Result<(), NetDevError>;

    /// Interrupt handler for network device.
    fn interrupt(&self, irq: u16) -> Result<(), NetDevError>;
    fn irqs(&self) -> Vec<u16>;
    fn rx_irq_to_que_id(&self, irq: u16) -> Option<usize>;

    /// Number of queues that the network device supports.
    /// This must be a power of 2:
    /// 0, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, etc.
    fn num_queues(&self) -> usize;

    /// Is the network device in polling mode?
    fn poll_mode(&self) -> bool {
        false
    }

    /// Poll the device in the network service.
    fn poll_in_service(&self) -> Result<(), NetDevError> {
        Err(NetDevError::DeviceError)
    }

    /// Poll the device.
    /// If the device is ready to do some action, return true.
    ///
    /// This function is called by CPU0 in the main loop.
    /// If `poll()` returns true, then the main loop will invoke a waker of
    /// a network service task.
    /// The network service task will call `poll_in_service()` later.
    fn poll(&self) -> bool {
        false
    }

    /// Get the millisecond tick count.
    /// If `None`, then the kernel does not call `tick()`.
    /// If `Some`, then the kernel calls `tick()` every `tick_msec()` milliseconds.
    fn tick_msec(&self) -> Option<u64> {
        None
    }

    /// `poll()` is used for polling mode, which is a alternative to interrupt mode.
    /// `tick()` is used for periodic tasks, such as status update.
    fn tick(&self) -> Result<(), NetDevError> {
        Ok(())
    }

    fn add_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError>;
    fn remove_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError>;

    fn get_segment_group(&self) -> Option<u16> {
        None
    }
}

impl Display for LinkStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LinkStatus::Up => write!(f, "Up"),
            LinkStatus::UpFullDuplex => write!(f, "Up (Full Duplex)"),
            LinkStatus::UpHalfDuplex => write!(f, "Up (Half Duplex)"),
            LinkStatus::Down => write!(f, "Down"),
            LinkStatus::Unknown => write!(f, "Unknown"),
        }
    }
}
