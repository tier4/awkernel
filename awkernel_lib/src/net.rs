use crate::sync::{mcs::MCSNode, mutex::Mutex};
use alloc::{
    borrow::Cow,
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    format,
    sync::Arc,
};
use core::{fmt::Display, net::Ipv4Addr};
use smoltcp::wire::{IpAddress, IpCidr};

use self::{
    if_net::IfNet,
    net_device::{LinkStatus, NetCapabilities, NetDevice},
    tcp::TcpPort,
};

#[cfg(not(feature = "std"))]
use alloc::{string::String, vec::Vec};

#[cfg(loom)]
use crate::sync::rwlock_dummy::RwLock;

#[cfg(not(loom))]
use crate::sync::rwlock::RwLock;

pub mod ether;
pub mod ethertypes;
mod if_net;
pub mod in_cksum;
pub mod ip;
pub mod ip_addr;
pub mod ipv6;
pub mod multicast;
pub mod net_device;
pub mod tcp;
pub mod tcp_listener;
pub mod tcp_stream;
pub mod udp;
pub mod udp_socket;

#[derive(Debug)]
pub enum NetManagerError {
    InvalidInterfaceID,
    InvalidIPv4Address,
    CannotFindInterface,
    PortInUse,
    SendError,
    RecvError,
    NotYetImplemented,
    InvalidPort,
    InvalidState,
    NoAvailablePort,
    InterfaceIsNotReady,
}

#[derive(Debug)]
pub struct IfStatus {
    pub interface_id: u64,
    pub device_name: Cow<'static, str>,
    pub ipv4_addrs: Vec<(Ipv4Addr, u8)>,
    pub ipv4_gateway: Option<Ipv4Addr>,
    pub link_speed_mbs: u64,
    pub link_status: LinkStatus,
    pub mac_address: [u8; 6],
    pub irqs: Vec<u16>,
    pub rx_irq_to_que_id: BTreeMap<u16, usize>,
    pub capabilities: NetCapabilities,
    pub poll_mode: bool,
    pub tick_msec: Option<u64>,
}

impl Display for IfStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut ipv4_addr = String::new();
        for (addr, plen) in self.ipv4_addrs.iter() {
            ipv4_addr.push_str(&format!("{}/{}", addr, plen));
        }

        let ipv4_gateway = match self.ipv4_gateway {
            Some(addr) => format!("{}", addr),
            None => String::from("None"),
        };

        write!(
            f,
            "[{}] {}:\r\n    IPv4 address: {}\r\n    IPv4 gateway: {}\r\n    MAC address: {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}\r\n    Link status: {}, Link speed: {} Mbps\r\n    Capabilities: {}\r\n    IRQs: {:?}\r\n    Poll mode: {}",
            self.interface_id,
            self.device_name,
            ipv4_addr,
            ipv4_gateway,
            self.mac_address[0],
            self.mac_address[1],
            self.mac_address[2],
            self.mac_address[3],
            self.mac_address[4],
            self.mac_address[5],
            self.link_status,
            self.link_speed_mbs,
            self.capabilities,
            self.irqs,
            self.poll_mode
        )
    }
}

static NET_MANAGER: RwLock<NetManager> = RwLock::new(NetManager {
    interfaces: BTreeMap::new(),
    interface_id: 0,
    udp_ports_ipv4: BTreeSet::new(),
    udp_port_ipv4_ephemeral: u16::MAX >> 2,
    udp_ports_ipv6: BTreeSet::new(),
    udp_port_ipv6_ephemeral: u16::MAX >> 2,
    tcp_ports_ipv4: BTreeMap::new(),
    tcp_port_ipv4_ephemeral: u16::MAX >> 2,
    tcp_ports_ipv6: BTreeMap::new(),
    tcp_port_ipv6_ephemeral: u16::MAX >> 2,
});

static IRQ_WAKERS: Mutex<BTreeMap<u16, IRQWaker>> = Mutex::new(BTreeMap::new());
static POLL_WAKERS: Mutex<BTreeMap<u64, IRQWaker>> = Mutex::new(BTreeMap::new());

pub struct NetManager {
    interfaces: BTreeMap<u64, Arc<IfNet>>,
    interface_id: u64,
    udp_ports_ipv4: BTreeSet<u16>,
    udp_port_ipv4_ephemeral: u16,
    udp_ports_ipv6: BTreeSet<u16>,
    udp_port_ipv6_ephemeral: u16,
    tcp_ports_ipv4: BTreeMap<u16, u64>,
    tcp_port_ipv4_ephemeral: u16,
    tcp_ports_ipv6: BTreeMap<u16, u64>,
    tcp_port_ipv6_ephemeral: u16,
}

impl NetManager {
    fn get_ephemeral_port_udp_ipv4(&mut self) -> Option<u16> {
        let mut ephemeral_port = None;
        for i in 0..(u16::MAX >> 2) {
            let port = self.udp_port_ipv4_ephemeral.wrapping_add(i);
            let port = if port == 0 { u16::MAX >> 2 } else { port };

            if !self.udp_ports_ipv4.contains(&port) {
                self.udp_ports_ipv4.insert(port);
                self.udp_port_ipv4_ephemeral = port;
                ephemeral_port = Some(port);
                break;
            }
        }

        ephemeral_port
    }

    #[inline(always)]
    fn set_port_in_use_udp_ipv4(&mut self, port: u16) {
        self.udp_ports_ipv4.insert(port);
    }

    #[inline(always)]
    fn is_port_in_use_udp_ipv4(&mut self, port: u16) -> bool {
        self.udp_ports_ipv4.contains(&port)
    }

    #[inline(always)]
    fn free_port_udp_ipv4(&mut self, port: u16) {
        self.udp_ports_ipv4.remove(&port);
    }

    fn get_ephemeral_port_udp_ipv6(&mut self) -> Option<u16> {
        let mut ephemeral_port = None;
        for i in 0..(u16::MAX >> 2) {
            let port = self.udp_port_ipv6_ephemeral.wrapping_add(i);
            let port = if port == 0 { u16::MAX >> 2 } else { port };

            if !self.udp_ports_ipv6.contains(&port) {
                self.udp_ports_ipv6.insert(port);
                self.udp_port_ipv4_ephemeral = port;
                ephemeral_port = Some(port);
                break;
            }
        }

        ephemeral_port
    }

    #[inline(always)]
    fn set_port_in_use_udp_ipv6(&mut self, port: u16) {
        self.udp_ports_ipv6.insert(port);
    }

    #[inline(always)]
    fn is_port_in_use_udp_ipv6(&mut self, port: u16) -> bool {
        self.udp_ports_ipv6.contains(&port)
    }

    #[inline(always)]
    fn free_port_udp_ipv6(&mut self, port: u16) {
        self.udp_ports_ipv6.remove(&port);
    }

    fn get_ephemeral_port_tcp_ipv4(&mut self) -> Option<TcpPort> {
        let mut ephemeral_port = None;
        for i in 0..(u16::MAX >> 2) {
            let port = self.tcp_port_ipv4_ephemeral.wrapping_add(i);
            let port = if port == 0 { u16::MAX >> 2 } else { port };

            let entry = self.tcp_ports_ipv4.entry(i);

            match entry {
                Entry::Occupied(_) => (),
                Entry::Vacant(e) => {
                    e.insert(1);
                    ephemeral_port = Some(TcpPort::new(port, true));
                    self.tcp_port_ipv4_ephemeral = port;
                    break;
                }
            }
        }

        ephemeral_port
    }

    #[inline(always)]
    fn is_port_in_use_tcp_ipv4(&mut self, port: u16) -> bool {
        self.tcp_ports_ipv4.contains_key(&port)
    }

    #[inline(always)]
    fn port_in_use_tcp_ipv4(&mut self, port: u16) -> TcpPort {
        if let Some(e) = self.tcp_ports_ipv4.get_mut(&port) {
            *e += 1;
        } else {
            self.tcp_ports_ipv4.insert(port, 1);
        }

        TcpPort::new(port, true)
    }

    #[inline(always)]
    fn decrement_port_in_use_tcp_ipv4(&mut self, port: u16) {
        if let Some(e) = self.tcp_ports_ipv4.get_mut(&port) {
            *e -= 1;
            if *e == 0 {
                self.tcp_ports_ipv4.remove(&port);
            }
        }
    }

    fn get_ephemeral_port_tcp_ipv6(&mut self) -> Option<TcpPort> {
        let mut ephemeral_port = None;
        for i in 0..(u16::MAX >> 2) {
            let port = self.tcp_port_ipv6_ephemeral.wrapping_add(i);
            let port = if port == 0 { u16::MAX >> 2 } else { port };

            let entry = self.tcp_ports_ipv6.entry(i);

            match entry {
                Entry::Occupied(_) => (),
                Entry::Vacant(e) => {
                    e.insert(1);
                    ephemeral_port = Some(TcpPort::new(port, false));
                    self.tcp_port_ipv6_ephemeral = port;
                    break;
                }
            }
        }

        ephemeral_port
    }

    #[inline(always)]
    fn is_port_in_use_tcp_ipv6(&mut self, port: u16) -> bool {
        self.tcp_ports_ipv6.contains_key(&port)
    }

    #[inline(always)]
    fn port_in_use_tcp_ipv6(&mut self, port: u16) -> TcpPort {
        if let Some(e) = self.tcp_ports_ipv6.get_mut(&port) {
            *e += 1;
        } else {
            self.tcp_ports_ipv6.insert(port, 1);
        }

        TcpPort::new(port, true)
    }

    #[inline(always)]
    fn decrement_port_in_use_tcp_ipv6(&mut self, port: u16) {
        if let Some(e) = self.tcp_ports_ipv6.get_mut(&port) {
            *e -= 1;
            if *e == 0 {
                self.tcp_ports_ipv6.remove(&port);
            }
        }
    }
}

pub fn get_interface(interface_id: u64) -> Result<IfStatus, NetManagerError> {
    let net_manager = NET_MANAGER.read();

    let if_net = net_manager
        .interfaces
        .get(&interface_id)
        .ok_or(NetManagerError::InvalidInterfaceID)?;

    let inner = &if_net.net_device;

    let mac_address = inner.mac_address();
    let link_speed_mbs = inner.link_speed();
    let link_status = inner.link_status();

    let mut ipv4_addrs = Vec::new();

    {
        let mut node = MCSNode::new();
        let interface = if_net.inner.lock(&mut node);

        for cidr in interface.interface.ip_addrs().iter() {
            if let IpAddress::Ipv4(addr) = cidr.address() {
                let addr = Ipv4Addr::new(addr.0[0], addr.0[1], addr.0[2], addr.0[3]);
                ipv4_addrs.push((addr, cidr.prefix_len()));
            }
        }
    }

    let irqs = inner.irqs();
    let poll_mode = inner.poll_mode();

    let mut rx_irq_to_que_id = BTreeMap::new();
    for irq in irqs.iter() {
        if let Some(que_id) = inner.rx_irq_to_que_id(*irq) {
            rx_irq_to_que_id.insert(*irq, que_id);
        };
    }

    let capabilities = inner.capabilities();

    let tick_msec = inner.tick_msec();

    let if_status = IfStatus {
        interface_id,
        device_name: inner.device_short_name(),
        ipv4_addrs,
        ipv4_gateway: None,
        link_status,
        link_speed_mbs,
        mac_address,
        irqs,
        rx_irq_to_que_id,
        capabilities,
        poll_mode,
        tick_msec,
    };

    Ok(if_status)
}

pub fn get_all_interface() -> Vec<IfStatus> {
    let net_manager = NET_MANAGER.read();

    let mut result = Vec::new();

    for id in net_manager.interfaces.keys() {
        if let Ok(if_status) = get_interface(*id) {
            result.push(if_status);
        }
    }

    result
}

enum IRQWaker {
    Waker(core::task::Waker),
    Interrupted,
}

pub fn add_interface(net_device: Arc<dyn NetDevice + Sync + Send>, vlan: Option<u16>) {
    let mut net_manager = NET_MANAGER.write();

    if net_manager.interface_id == u64::MAX {
        panic!("interface id overflow");
    }

    let id = net_manager.interface_id;
    net_manager.interface_id += 1;

    let if_net = Arc::new(IfNet::new(net_device, vlan));

    net_manager.interfaces.insert(id, if_net);
}

pub fn add_ipv4_addr(interface_id: u64, addr: Ipv4Addr, prefix_len: u8) {
    let net_manager = NET_MANAGER.read();

    let Some(if_net) = net_manager.interfaces.get(&interface_id) else {
        return;
    };

    let mut node = MCSNode::new();
    let mut inner = if_net.inner.lock(&mut node);

    let octets = addr.octets();

    inner.interface.update_ip_addrs(|ip_addrs| {
        if let Err(e) = ip_addrs.push(IpCidr::new(
            IpAddress::v4(octets[0], octets[1], octets[2], octets[3]),
            prefix_len,
        )) {
            log::error!("add_ipv4_addr: {}", e);
        }
    });
}

/// Service routine for network device interrupt.
/// This routine should be called by interrupt handlers provided by device drivers.
pub fn net_interrupt(irq: u16) {
    let mut node = MCSNode::new();
    let mut w = IRQ_WAKERS.lock(&mut node);

    match w.entry(irq) {
        Entry::Occupied(e) => {
            if matches!(e.get(), IRQWaker::Waker(_)) {
                let IRQWaker::Waker(w) = e.remove() else {
                    return;
                };

                w.wake();
            }
        }
        Entry::Vacant(e) => {
            e.insert(IRQWaker::Interrupted);
        }
    }
}

/// Register a waker for a network device interrupt service.
///
/// The old waker will be replaced.
/// The waker will be called when the network device interrupt occurs once
/// and it will be removed after it is called.
///
/// Returns true if the waker is registered successfully.
/// Returns false if the interrupt occurred before.
pub fn register_waker_for_network_interrupt(irq: u16, waker: core::task::Waker) -> bool {
    let mut node = MCSNode::new();
    let mut w = IRQ_WAKERS.lock(&mut node);

    let entry = w.entry(irq);

    match entry {
        Entry::Occupied(mut e) => {
            if matches!(e.get(), IRQWaker::Interrupted) {
                e.remove();
                false
            } else {
                e.insert(IRQWaker::Waker(waker));
                true
            }
        }
        Entry::Vacant(e) => {
            e.insert(IRQWaker::Waker(waker));
            true
        }
    }
}

/// Register a waker for a poll service.
///
/// The old waker will be replaced.
/// The waker will be called when the network device has some events to be processed
/// and it will be removed after it is called.
///
/// Returns true if the waker is registered successfully.
/// Returns false if there are some events.
pub fn register_waker_for_poll(interface_id: u64, waker: core::task::Waker) -> bool {
    let mut node = MCSNode::new();
    let mut w = POLL_WAKERS.lock(&mut node);

    let entry = w.entry(interface_id);

    match entry {
        Entry::Occupied(mut e) => {
            if matches!(e.get(), IRQWaker::Interrupted) {
                e.remove();
                false
            } else {
                e.insert(IRQWaker::Waker(waker));
                true
            }
        }
        Entry::Vacant(e) => {
            e.insert(IRQWaker::Waker(waker));
            true
        }
    }
}

/// Because some devices need to poll the network device to process some events,
/// this function should be called by the network service.
///
/// Usually, `poll_interface()` is for receiving and reading packets,
/// and `tick_interface()` is for updating status.
pub fn tick_interface(interface_id: u64) {
    let interface = {
        let net_manager = NET_MANAGER.read();

        let Some(interface) = net_manager.interfaces.get(&interface_id) else {
            return;
        };

        interface.clone()
    };

    let _ = interface.net_device.tick();
    interface.tick_rx_poll_mode();
}

/// If some packets are processed, true is returned.
/// If true is returned, the caller should call this function again.
///
/// `poll_interface()` should be called by a network service.
pub fn poll_interface(interface_id: u64) -> bool {
    let interface = {
        let net_manager = NET_MANAGER.read();

        let Some(interface) = net_manager.interfaces.get(&interface_id) else {
            return false;
        };

        interface.clone()
    };

    let _ = interface.net_device.poll_in_service();
    interface.poll_rx_poll_mode()
}

/// Check if there are some events to be processed.
/// `poll()` should be called by CPU0.
///
/// 1. `NetManager.read()`
/// 2. `POLL_WAKERS.lock()`
pub fn poll() {
    let net_manager = NET_MANAGER.read();

    for (interface_id, if_net) in net_manager.interfaces.iter() {
        if if_net.is_poll_mode && if_net.net_device.poll() {
            let mut node = MCSNode::new();
            let mut w = POLL_WAKERS.lock(&mut node);

            match w.entry(*interface_id) {
                Entry::Occupied(e) => {
                    if matches!(e.get(), IRQWaker::Waker(_)) {
                        let IRQWaker::Waker(w) = e.remove() else {
                            continue;
                        };

                        w.wake();
                    }
                }
                Entry::Vacant(e) => {
                    e.insert(IRQWaker::Interrupted);
                }
            }
        }
    }
}

/// If some packets are processed, true is returned.
/// If true is returned, the caller should call this function again.
pub fn handle_interrupt(interface_id: u64, irq: u16) -> bool {
    let interface = {
        let net_manager = NET_MANAGER.read();

        let Some(interface) = net_manager.interfaces.get(&interface_id) else {
            return false;
        };

        interface.clone()
    };

    let _ = interface.net_device.interrupt(irq);
    interface.poll_rx_irq(irq)
}

/// Enable the network interface.
pub fn up(interface_id: u64) -> Result<(), NetManagerError> {
    let net_manager = NET_MANAGER.read();

    let Some(if_net) = net_manager.interfaces.get(&interface_id) else {
        return Err(NetManagerError::InvalidInterfaceID);
    };

    let _ = if_net.net_device.up();

    Ok(())
}

/// Disable the network interface.
pub fn down(interface_id: u64) -> Result<(), NetManagerError> {
    let net_manager = NET_MANAGER.read();

    let Some(if_net) = net_manager.interfaces.get(&interface_id) else {
        return Err(NetManagerError::InvalidInterfaceID);
    };

    let _ = if_net.net_device.down();

    Ok(())
}

pub fn set_default_gateway_ipv4(
    interface_id: u64,
    gateway: Ipv4Addr,
) -> Result<(), NetManagerError> {
    let net_manager = NET_MANAGER.read();

    let Some(if_net) = net_manager.interfaces.get(&interface_id) else {
        return Err(NetManagerError::InvalidInterfaceID);
    };

    let mut node = MCSNode::new();
    let mut inner = if_net.inner.lock(&mut node);

    let octets = gateway.octets();
    inner.set_default_gateway_ipv4(smoltcp::wire::Ipv4Address::new(
        octets[0], octets[1], octets[2], octets[3],
    ));

    Ok(())
}

pub fn get_default_gateway_ipv4(interface_id: u64) -> Result<Option<Ipv4Addr>, NetManagerError> {
    let net_manager = NET_MANAGER.read();

    let Some(if_net) = net_manager.interfaces.get(&interface_id) else {
        return Err(NetManagerError::InvalidInterfaceID);
    };

    let mut node = MCSNode::new();
    let inner = if_net.inner.lock(&mut node);

    if let Some(addr) = inner.get_default_gateway_ipv4() {
        Ok(Some(Ipv4Addr::new(
            addr.0[0], addr.0[1], addr.0[2], addr.0[3],
        )))
    } else {
        Ok(None)
    }
}
