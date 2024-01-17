use crate::sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock};
use alloc::{collections::BTreeMap, format, string::String, sync::Arc, vec, vec::Vec};
use bitflags::bitflags;
use core::{fmt::Display, net::Ipv4Addr};
use smoltcp::{
    iface::{Config, Interface, SocketSet},
    phy::{self, DeviceCapabilities},
    time::Instant,
    wire::{EthernetAddress, HardwareAddress, IpAddress, IpCidr, Ipv4Address},
};

pub mod ether;
pub mod ethertypes;
pub mod ip;
pub mod ipv6;
pub mod multicast;
pub mod tcp;
pub mod udp;

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

#[derive(Debug, Clone)]
pub struct EtherFrameBuf {
    pub data: Vec<u8>,
    pub vlan: Option<u16>,
}

#[derive(Debug, Clone)]
pub struct EtherFrameRef<'a> {
    pub data: &'a [u8],
    pub vlan: Option<u16>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NetDevError {
    AlreadyUp,
    AlreadyDown,
    DeviceError,
    MulticastAddrError,
}

/// Because the network will have multiple queues
/// and the queues will be processed in parallel,
/// the network device must be thread-safe.
///
/// # Example
///
/// ```
/// use awkernel_lib::{net::NetDevice, sync::{mutex::Mutex, rwlock:RwLock, mcs::MCSNode}}};
///
/// const NUM_QUEUE: usize = 4;
///
/// struct MyNetDeviceInner;
/// struct MyNetDeviceQueue;
///
/// struct MyNetDevice {
///     inner: RwLock<MyNetDeviceInner>,
///     queue: [Mutex<MyNetDeviceQueue>; NUM_QUEUE]
/// }
///
/// impl NetDevice for MyNetDevice {
///      fn recv(&self) -> Option<Vec<u8>> {
///           let inner = self.inner.read(); // Read-lock
///
///           let mut node = MCSNode::new();
///           let mut que = self.queue[0].lock(); // Lock
///
///           // do receive
///      }
///
///     fn up(&self) -> Result<(), NetDevError> {
///         let mut inner = self.inner.write(); // Write-lock
///
///         // do up
///     }
///
///     fn down(&self) -> Result<(), NetDevError> { todo!() }
///     fn send(&self, data: &[u8]) -> Option<()> { todo!() }
///     fn flags(&self) -> NetFlags { todo!() }
///     fn capabilities(&self) -> NetCapabilities { todo!() }
///     fn link_speed(&self) -> u64 { todo!() }
///     fn can_send(&self) -> bool { todo!() }
///     fn mac_address(&self) -> [u8; 6] { todo!() }
///     fn link_up(&self) -> bool { todo!() }
///     fn full_duplex(&self) -> bool { todo!() }
///     fn device_short_name(&self) -> &'static str { todo!() }
///     fn add_multicast_addr_ipv4(&self, addr: Ipv4Addr) -> Result<(), NetDevError> { todo!() }
///     fn add_multicast_range_ipv4(&self, start: Ipv4Addr, end: Ipv4Addr) -> Result<(), NetDevError> { todo!() }
///     fn remove_multicast_addr_ipv4(&self, addr: Ipv4Addr) -> Result<(), NetDevError> { todo!() }
///     fn remove_multicast_range_ipv4(&self, start: Ipv4Addr, end: Ipv4Addr) -> Result<(), NetDevError> { todo!() }
/// }
/// ```
pub trait NetDevice {
    fn recv(&self) -> Option<EtherFrameBuf>;
    fn send(&self, data: EtherFrameRef) -> Option<()>;

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

    /// Interrupt handler for network device.
    fn interrupt(&self, irq: u16) -> Result<(), NetDevError>;
    fn irqs(&self) -> Vec<u16>;

    fn add_multicast_addr_ipv4(&self, addr: Ipv4Addr) -> Result<(), NetDevError>;
    fn add_multicast_range_ipv4(&self, start: Ipv4Addr, end: Ipv4Addr) -> Result<(), NetDevError>;

    fn remove_multicast_addr_ipv4(&self, addr: Ipv4Addr) -> Result<(), NetDevError>;
    fn remove_multicast_range_ipv4(
        &self,
        start: Ipv4Addr,
        end: Ipv4Addr,
    ) -> Result<(), NetDevError>;
}

pub struct NetDriver {
    inner: Arc<dyn NetDevice + Sync + Send>,
    vlan: Option<u16>,
}

pub struct NetDriverRef<'a> {
    ref_net_driver: &'a NetDriver,
}

impl<'a> phy::Device for NetDriverRef<'a> {
    type RxToken<'b> = NRxToken where Self : 'b;
    type TxToken<'b> = NTxToken where Self: 'b;
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
        let data = self.ref_net_driver.inner.recv()?.data;
        Some((
            NRxToken { data },
            NTxToken {
                device: self.ref_net_driver.inner.clone(),
                vlan: self.ref_net_driver.vlan,
            },
        ))
    }

    //  The real  packet transmission occurrs when the token is consumed.
    fn transmit(&mut self, _timestamp: smoltcp::time::Instant) -> Option<Self::TxToken<'_>> {
        if !self.ref_net_driver.inner.can_send() {
            return None;
        }

        Some(NTxToken {
            device: self.ref_net_driver.inner.clone(),
            vlan: self.ref_net_driver.vlan,
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
        self.device.send(EtherFrameRef {
            data: &buffer,
            vlan: self.vlan,
        });
        result
    }
}

pub struct NTxToken {
    device: Arc<dyn NetDevice + Send>,
    vlan: Option<u16>,
}

pub struct NetIf {
    driver: NetDriver,
    interface: Mutex<Interface>,
    ipv4_gateway: Mutex<Option<Ipv4Addr>>, // default gateway
    socket_set: Mutex<SocketSet<'static>>,
}

#[derive(Debug)]
pub enum NetManagerError {
    InvalidInterfaceID,
}

#[derive(Debug)]
pub struct IfStatus {
    pub device_name: &'static str,
    pub ipv4_addrs: Vec<(Ipv4Addr, u8)>,
    pub ipv4_gateway: Option<Ipv4Addr>,
    pub link_up: bool,
    pub link_speed_mbs: u64,
    pub full_duplex: bool,
    pub mac_address: [u8; 6],
}

impl Display for IfStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut ipv4_addr = String::new();
        for (addr, plen) in self.ipv4_addrs.iter() {
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
    interfaces: Vec<Arc<NetIf>>,
    irq_to_interfaces: BTreeMap<u16, Arc<NetIf>>,
}

impl NetManager {
    const fn new() -> Self {
        Self {
            interfaces: Vec::new(),
            irq_to_interfaces: BTreeMap::new(),
        }
    }

    pub fn add_interface(&mut self, inner: Arc<dyn NetDevice + Sync + Send>, vlan: Option<u16>) {
        let hardware_addr = HardwareAddress::Ethernet(EthernetAddress(inner.mac_address()));
        let config = Config::new(hardware_addr);
        let timestamp = Instant::from_micros(crate::delay::uptime() as i64);
        let driver = NetDriver { inner, vlan };
        let mut device_ref = NetDriverRef {
            ref_net_driver: &driver,
        };

        let interface = Mutex::new(Interface::new(config, &mut device_ref, timestamp));

        let value = Arc::new(NetIf {
            driver,
            interface,
            ipv4_gateway: Mutex::new(None),
            socket_set: Mutex::new(SocketSet::new(vec![])),
        });

        for irq in value.driver.inner.irqs() {
            self.irq_to_interfaces.insert(irq, value.clone());
        }

        self.interfaces.push(value);
    }

    pub fn add_ipv4_addr(
        &mut self,
        mac: &[u8; 6],
        addr: Ipv4Addr,
        plen: u8,
    ) -> Result<(), NetManagerError> {
        let netif = self
            .interfaces
            .iter_mut()
            .find(|d| d.driver.inner.mac_address() == *mac)
            .ok_or(NetManagerError::InvalidInterfaceID)?;

        let mut node = MCSNode::new();
        let mut interface = netif.interface.lock(&mut node);
        interface.update_ip_addrs(|ip_addrs| {
            let octets = addr.octets();

            ip_addrs
                .push(IpCidr::new(
                    IpAddress::v4(octets[0], octets[1], octets[2], octets[3]),
                    plen,
                ))
                .unwrap();
        });

        Ok(())
    }

    pub fn set_ipv4_gateway(
        &mut self,
        mac: &[u8; 6],
        addr: Ipv4Addr,
    ) -> Result<(), NetManagerError> {
        let netif = self
            .interfaces
            .iter_mut()
            .find(|d| d.driver.inner.mac_address() == *mac)
            .ok_or(NetManagerError::InvalidInterfaceID)?;

        let octets = addr.octets();
        {
            let mut node = MCSNode::new();
            let mut interface = netif.interface.lock(&mut node);

            if interface
                .routes_mut()
                .add_default_ipv4_route(Ipv4Address::new(
                    octets[0], octets[1], octets[2], octets[3],
                ))
                .is_err()
            {
                log::error!("set default IPv4 route error, MAC = {:x?}", mac);
            }
        }

        let mut node = MCSNode::new();
        let mut ipv4_gateway = netif.ipv4_gateway.lock(&mut node);
        *ipv4_gateway = Some(addr);

        Ok(())
    }

    pub fn get_interfaces(&self) -> Vec<IfStatus> {
        let mut result = Vec::new();

        for netif in self.interfaces.iter() {
            let inner = &netif.driver.inner;
            let mac_address = inner.mac_address();
            let link_up = inner.link_up();
            let link_speed_mbs = inner.link_speed();
            let full_duplex = inner.full_duplex();

            let mut ipv4_addrs = Vec::new();

            {
                let mut node = MCSNode::new();
                let interface = netif.interface.lock(&mut node);
                for cidr in interface.ip_addrs().iter() {
                    if let IpAddress::Ipv4(addr) = cidr.address() {
                        let addr = Ipv4Addr::new(addr.0[0], addr.0[1], addr.0[2], addr.0[3]);
                        ipv4_addrs.push((addr, cidr.prefix_len()));
                    }
                }
            }

            let mut node = MCSNode::new();
            let ipv4_gateway = *netif.ipv4_gateway.lock(&mut node);

            let device_name = inner.device_short_name();

            result.push(IfStatus {
                device_name,
                ipv4_addrs,
                ipv4_gateway,
                link_up,
                link_speed_mbs,
                full_duplex,
                mac_address,
            });
        }

        result
    }
}

pub static NET_MANAGER: RwLock<NetManager> = RwLock::new(NetManager::new());
pub static IRQS: Mutex<Vec<u16>> = Mutex::new(Vec::new());
pub static WAKER: Mutex<Option<core::task::Waker>> = Mutex::new(None);

pub fn get_interfaces() -> Vec<IfStatus> {
    let net_manager = NET_MANAGER.read();
    net_manager.get_interfaces()
}

pub fn add_interface(inner: Arc<dyn NetDevice + Sync + Send>, vlan: Option<u16>) {
    let mut net_manager = NET_MANAGER.write();
    net_manager.add_interface(inner, vlan);
}

/// Service routine for network device interrupt.
/// This routine should be called by interrupt handlers provided by device drivers.
pub fn netif_interrupt(irq: u16) {
    {
        let mut node = MCSNode::new();
        let mut irqs = IRQS.lock(&mut node);
        irqs.push(irq);
    }

    let mut node = MCSNode::new();
    let mut waker = WAKER.lock(&mut node);
    if let Some(waker) = waker.take() {
        waker.wake();
    }
}

/// Register a waker for a network device interrupt service.
///
/// The old waker will be replaced.
/// The waker will be called when the network device interrupt occurs once
/// and it will be removed after it is called.
pub fn register_network_interrupt_service_waker(waker: core::task::Waker) {
    let mut node = MCSNode::new();
    let mut w = WAKER.lock(&mut node);
    *w = Some(waker);
}

pub fn has_pending_irqs() -> bool {
    let mut node = MCSNode::new();
    let irqs = IRQS.lock(&mut node);
    !irqs.is_empty()
}

/// Handle network device interrupt actually.
pub fn network_interrupt_service() {
    let irqs = {
        let mut node = MCSNode::new();
        let mut irqs = IRQS.lock(&mut node);
        let mut new_irqs = Vec::new();
        core::mem::swap(irqs.as_mut(), &mut new_irqs);
        new_irqs
    };

    let net_manager = NET_MANAGER.read();

    {
        for irq in irqs.iter() {
            if let Some(interface) = net_manager.irq_to_interfaces.get(irq) {
                if let Err(e) = interface.driver.inner.interrupt(*irq) {
                    log::error!(
                        "{}: netif interrupt error, {:?}",
                        interface.driver.inner.device_short_name(),
                        e
                    );
                } else {
                    let timestamp = Instant::from_micros(crate::delay::uptime() as i64);
                    let mut device_ref = NetDriverRef {
                        ref_net_driver: &interface.driver,
                    };

                    let mut node = MCSNode::new();
                    let mut iface = interface.interface.lock(&mut node);

                    let mut node = MCSNode::new();
                    let mut socket_set = interface.socket_set.lock(&mut node);

                    iface.poll(timestamp, &mut device_ref, &mut socket_set);
                }
            }
        }
    }
}
