use crate::sync::{mcs::MCSNode, mutex::Mutex};
use alloc::{boxed::Box, format, string::String, sync::Arc, vec, vec::Vec};
use bitflags::bitflags;
use core::{fmt::Display, net::Ipv4Addr};
use smoltcp::{
    iface::{Config, Interface},
    phy::{self, DeviceCapabilities},
    time::Instant,
    wire::{EthernetAddress, HardwareAddress},
};

pub mod ethertypes;
pub mod multicast;

bitflags! {
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

pub trait NetDevice {
    fn recv(&mut self) -> Option<Vec<u8>>;
    fn send(&mut self, data: &[u8]) -> Option<()>;

    fn flags(&self) -> NetFlags;
    fn capabilities(&self) -> NetCapabilities;

    /// Link speed in Mbps.
    fn link_speed(&self) -> u64;

    fn can_send(&self) -> bool;
    fn mac_address(&self) -> [u8; 6];
    fn link_up(&self) -> bool;
    fn full_duplex(&self) -> bool;

    fn device_short_name(&self) -> &'static str;

    fn up(&mut self) -> Result<(), NetDevError>;
    fn down(&mut self) -> Result<(), NetDevError>;

    fn add_multicast_addr_ipv4(&mut self, addr: Ipv4Addr) -> Result<(), NetDevError>;
    fn add_multicast_range_ipv4(
        &mut self,
        start: Ipv4Addr,
        end: Ipv4Addr,
    ) -> Result<(), NetDevError>;
}

#[derive(Clone)]
pub struct NetDriver {
    inner: Arc<Mutex<Box<dyn NetDevice + Send>>>,
}

impl phy::Device for NetDriver {
    type RxToken<'a> = NRxToken where Self : 'a;
    type TxToken<'a> = NTxToken where Self: 'a;
    fn capabilities(&self) -> phy::DeviceCapabilities {
        let mut cap = DeviceCapabilities::default();
        cap.max_transmission_unit = 1500;
        cap.max_burst_size = Some(64);
        cap
    }

    //  The additional transmit token makes it possible to generate a reply packet
    //  based on the contents of the received packet, without heap allocation.
    fn receive(
        &mut self,
        _timestamp: smoltcp::time::Instant,
    ) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        let node = &mut MCSNode::new();
        let mut inner = self.inner.lock(node);
        let data = inner.recv()?;
        Some((
            NRxToken { data },
            NTxToken {
                device: self.inner.clone(),
            },
        ))
    }

    //  The real  packet transmission occurrs when the token is consumed.
    fn transmit(&mut self, _timestamp: smoltcp::time::Instant) -> Option<Self::TxToken<'_>> {
        let node = &mut MCSNode::new();
        let inner = self.inner.lock(node);

        if !inner.can_send() {
            return None;
        }

        Some(NTxToken {
            device: self.inner.clone(),
        })
    }
}

pub struct NRxToken {
    data: Vec<u8>,
}

impl phy::RxToken for NRxToken {
    /// Store packet data into the buffer.
    /// Closure f will map the raw bytes to the form that
    /// could be used in the higher layer of `smoltcp`.
    fn consume<R, F>(mut self, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        f(&mut self.data)
    }
}

impl phy::TxToken for NTxToken {
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        // allocate a buffer for raw data
        let mut buffer = vec![0; len];
        // construct packet in buffer
        let result = f(&mut buffer[0..len]);
        // send the buffer
        let node = &mut MCSNode::new();
        let mut inner = self.device.lock(node);
        inner.send(&buffer);
        result
    }
}

pub struct NTxToken {
    device: Arc<Mutex<Box<dyn NetDevice + Send>>>,
}

#[derive(Clone)]
pub struct NetIf {
    driver: NetDriver,
    ipv4_addr: Vec<(Ipv4Addr, u8)>, // (address, prefix length)
    ipv4_gateway: Option<Ipv4Addr>,
}

#[derive(Debug)]
pub enum NetManagerError {
    InvalidInterfaceID,
}

#[derive(Debug)]
pub struct IfStatus {
    pub device_name: &'static str,
    pub ipv4_addr: Vec<(Ipv4Addr, u8)>,
    pub ipv4_gateway: Option<Ipv4Addr>,
    pub link_up: bool,
    pub link_speed_mbs: u64,
    pub full_duplex: bool,
    pub mac_address: [u8; 6],
}

impl Display for IfStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut ipv4_addr = String::new();
        for (addr, plen) in self.ipv4_addr.iter() {
            ipv4_addr.push_str(&format!("{}/{}\r\n", addr, plen));
        }

        let ipv4_gateway = match self.ipv4_gateway {
            Some(addr) => format!("{}", addr),
            None => String::from("None"),
        };

        write!(
            f,
            "{}:\r\n    IPv4 address: {}\r\n    IPv4 gateway: {}\r\n    MAC address: {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}\r\n    Link up: {}, Link speed: {} Mbps, Full duplex: {}",
            self.device_name,
            ipv4_addr,
            ipv4_gateway,
            self.mac_address[0],
            self.mac_address[1],
            self.mac_address[2],
            self.mac_address[3],
            self.mac_address[4],
            self.mac_address[5],
            self.link_up,
            self.link_speed_mbs,
            self.full_duplex,
        )
    }
}

pub struct NetManager {
    drivers: Vec<NetIf>,
}

impl NetManager {
    const fn new() -> Self {
        Self {
            drivers: Vec::new(),
        }
    }

    pub fn add_interface(&mut self, inner: Arc<Mutex<Box<dyn NetDevice + Send>>>) {
        let value = NetIf {
            driver: NetDriver {
                inner: inner.clone(),
            },
            ipv4_addr: Vec::new(),
            ipv4_gateway: None,
        };

        self.drivers.push(value);
    }

    pub fn add_ipv4_addr(
        &mut self,
        mac: &[u8; 6],
        addr: Ipv4Addr,
        plen: u8,
    ) -> Result<(), NetManagerError> {
        let netif = self
            .drivers
            .iter_mut()
            .find(|d| {
                let mut node = MCSNode::new();
                let result = d.driver.inner.lock(&mut node).mac_address() == *mac;
                result
            })
            .ok_or(NetManagerError::InvalidInterfaceID)?;

        netif.ipv4_addr.push((addr, plen));

        Ok(())
    }

    pub fn set_ipv4_gateway(&mut self, mac: &[u8; 6], addr: Ipv4Addr) {
        let netif = self
            .drivers
            .iter_mut()
            .find(|d| {
                let mut node = MCSNode::new();
                let result = d.driver.inner.lock(&mut node).mac_address() == *mac;
                result
            })
            .unwrap();

        netif.ipv4_gateway = Some(addr);
    }

    pub fn get_interfaces(&self) -> Vec<IfStatus> {
        let mut result = Vec::new();

        for netif in self.drivers.iter() {
            let mut node = MCSNode::new();
            let inner = netif.driver.inner.lock(&mut node);
            let mac_address = inner.mac_address();
            let link_up = inner.link_up();
            let link_speed_mbs = inner.link_speed();
            let full_duplex = inner.full_duplex();

            let ipv4_addr = netif.ipv4_addr.clone();
            let ipv4_gateway = netif.ipv4_gateway;
            let device_name = inner.device_short_name();

            result.push(IfStatus {
                device_name,
                ipv4_addr,
                ipv4_gateway,
                link_up,
                link_speed_mbs,
                full_duplex,
                mac_address,
            });
        }

        result
    }

    // TODO: fix
    fn create_netif(&mut self) -> Option<(NetDriver, Interface)> {
        if self.drivers.is_empty() {
            return None;
        }

        // TODO: decide how to choose the driver
        let mut device = NetDriver {
            inner: self.drivers[0].driver.inner.clone(),
        };

        let node = &mut MCSNode::new();
        let addr = device.inner.lock(node).mac_address();
        let hardware_addr = HardwareAddress::Ethernet(EthernetAddress(addr));
        let config = Config::new(hardware_addr);
        let timestamp = Instant::from_micros(crate::delay::uptime() as i64);
        let iface = Interface::new(config, &mut device, timestamp);
        Some((device, iface))
    }

    // TODO: fix
    pub fn get_netif() -> Option<(NetDriver, Interface)> {
        let node = &mut MCSNode::new();
        let mut net_manager = NET_MANAGER.lock(node);
        net_manager.create_netif()
    }
}

pub static NET_MANAGER: Mutex<NetManager> = Mutex::new(NetManager::new());

pub fn get_interfaces() -> Vec<IfStatus> {
    let node = &mut MCSNode::new();
    let net_manager = NET_MANAGER.lock(node);
    net_manager.get_interfaces()
}
