use crate::sync::{mcs::MCSNode, mutex::Mutex};
use alloc::{collections::BTreeMap, format, string::String, sync::Arc, vec, vec::Vec};
use bitflags::bitflags;
use core::{fmt::Display, future::Future, net::Ipv4Addr};
use smoltcp::{
    iface::{Config, Interface},
    phy::{self, DeviceCapabilities},
    time::Instant,
    wire::{EthernetAddress, HardwareAddress},
};

pub mod ether;
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
    fn recv(&self) -> Option<Vec<u8>>;
    fn send(&self, data: &[u8]) -> Option<()>;

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
        let data = self.inner.recv()?;
        Some((
            NRxToken { data },
            NTxToken {
                device: self.inner.clone(),
            },
        ))
    }

    //  The real  packet transmission occurrs when the token is consumed.
    fn transmit(&mut self, _timestamp: smoltcp::time::Instant) -> Option<Self::TxToken<'_>> {
        if !self.inner.can_send() {
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
        self.device.send(&buffer);
        result
    }
}

pub struct NTxToken {
    device: Arc<dyn NetDevice + Send>,
}

pub struct NetIf {
    driver: NetDriver,
    ipv4_addr: Mutex<Vec<(Ipv4Addr, u8)>>, // (address, prefix length)
    ipv4_gateway: Mutex<Option<Ipv4Addr>>, // default gateway
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
    drivers: Vec<Arc<NetIf>>,
    irq_to_drivers: BTreeMap<u16, Arc<NetIf>>,
}

impl NetManager {
    const fn new() -> Self {
        Self {
            drivers: Vec::new(),
            irq_to_drivers: BTreeMap::new(),
        }
    }

    pub fn add_interface(&mut self, inner: Arc<dyn NetDevice + Sync + Send>) {
        let value = NetIf {
            driver: NetDriver { inner },
            ipv4_addr: Mutex::new(Vec::new()),
            ipv4_gateway: Mutex::new(None),
        };

        self.drivers.push(Arc::new(value));
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
            .find(|d| d.driver.inner.mac_address() == *mac)
            .ok_or(NetManagerError::InvalidInterfaceID)?;

        let mut node = MCSNode::new();
        let mut ipv4_addr = netif.ipv4_addr.lock(&mut node);
        ipv4_addr.push((addr, plen));

        Ok(())
    }

    pub fn set_ipv4_gateway(&mut self, mac: &[u8; 6], addr: Ipv4Addr) {
        let netif = self
            .drivers
            .iter_mut()
            .find(|d| {
                // let mut node = MCSNode::new();
                // let result = d.driver.inner.lock(&mut node).mac_address() == *mac;
                d.driver.inner.mac_address() == *mac
            })
            .unwrap();

        let mut node = MCSNode::new();
        let mut ipv4_gateway = netif.ipv4_gateway.lock(&mut node);
        *ipv4_gateway = Some(addr);
    }

    pub fn get_interfaces(&self) -> Vec<IfStatus> {
        let mut result = Vec::new();

        for netif in self.drivers.iter() {
            let inner = &netif.driver.inner;
            let mac_address = inner.mac_address();
            let link_up = inner.link_up();
            let link_speed_mbs = inner.link_speed();
            let full_duplex = inner.full_duplex();

            let mut node = MCSNode::new();
            let ipv4_addr = netif.ipv4_addr.lock(&mut node).clone();

            let mut node = MCSNode::new();
            let ipv4_gateway = netif.ipv4_gateway.lock(&mut node).clone();

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

        let addr = device.inner.mac_address();
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
pub static IRQS: Mutex<Vec<u16>> = Mutex::new(Vec::new());
pub static WAKER: Mutex<Option<core::task::Waker>> = Mutex::new(None);

pub fn get_interfaces() -> Vec<IfStatus> {
    let node = &mut MCSNode::new();
    let net_manager = NET_MANAGER.lock(node);
    net_manager.get_interfaces()
}

/// Service routine for network device interrupt.
pub fn netif_interrupt(irq: u16) {
    let mut node = &mut MCSNode::new();
    if let Some(waker) = WAKER.lock(&mut node).take() {
        waker.wake();
    }

    log::debug!("netif interrupt: {}", irq);
}

/// Handle network device interrupt actually.
pub async fn network_interrupt_service() {
    loop {
        let srv = NetworkInterruptService;
        srv.await;

        let mut node = &mut MCSNode::new();
        let net_manager = NET_MANAGER.lock(&mut node);

        let mut node = &mut MCSNode::new();
        for irq in IRQS.lock(&mut node).iter() {
            if let Some(driver) = net_manager.irq_to_drivers.get(irq) {
                driver.driver.inner.interrupt(*irq).unwrap();
            }
        }
    }
}

struct NetworkInterruptService;

impl Future for NetworkInterruptService {
    type Output = ();

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let waker = cx.waker().clone();

        let mut node = &mut MCSNode::new();
        let mut w = WAKER.lock(&mut node);
        *w = Some(waker);

        core::task::Poll::Pending
    }
}
