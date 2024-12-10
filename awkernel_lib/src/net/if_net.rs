//! # Network Interface Module
//!
//! This module provides the network interface module.
//!
//! `IfNet` is a structure that manages the network interface.
//! `NetDriver` is a structure that manages the network driver.
//!
//!　These structures contain the following mutex-protected fields:
//!
//! 1. `NetDriver::rx_ringq`
//! 2. `IfNet::tx_ringq`
//! 3. `IfNet::inner`
//!
//! These mutexes must be locked in the order shown above.

use core::net::Ipv4Addr;

use alloc::{
    collections::{btree_map, btree_set::BTreeSet, BTreeMap},
    sync::Arc,
};
use awkernel_async_lib_verified::ringq::RingQ;
use smoltcp::{
    iface::{Config, Interface, MulticastError, SocketSet},
    phy::{self, Checksum, Device, DeviceCapabilities},
    time::Instant,
    wire::HardwareAddress,
};
use x86_64::instructions::port;

#[cfg(not(loom))]
use crate::sync::rwlock::RwLock;
use crate::{
    addr::{virt_addr, Addr},
    dma_pool::DMAPool,
    paging::PAGESIZE,
    sync::{mcs::MCSNode, mutex::Mutex},
};

use super::{
    ether::{extract_headers, NetworkHdr, TransportHdr, ETHER_ADDR_LEN},
    multicast::ipv4_addr_to_mac_addr,
    net_device::{
        EtherFrameBuf, EtherFrameDMA, EtherFrameDMAcsum, EtherFrameRef, NetCapabilities, NetDevice,
        PacketHeaderFlags,
    },
    NetManagerError,
};

use super::super::delay::uptime_nano;

#[cfg(not(feature = "std"))]
use alloc::{vec, vec::Vec};

enum TransmitWakeState {
    None,
    Notified,
    Wake(core::task::Waker),
}

struct NetDriver {
    inner: Arc<dyn NetDevice + Sync + Send>,
    rx_que_id: usize,

    rx_ringq: Mutex<RingQ<EtherFrameDMA>>,
}

struct NetDriverRef<'a> {
    inner: &'a Arc<dyn NetDevice + Sync + Send>,

    rx_ringq: Option<&'a mut RingQ<EtherFrameDMA>>,
    tx_ringq: &'a mut RingQ<(DMAPool<[u8; PAGESIZE]>, usize)>,
}

static COUNT: Mutex<Vec<u32>> = Mutex::new(Vec::new());
static RECV_COUNT: Mutex<Vec<u32>> = Mutex::new(Vec::new());

impl NetDriverRef<'_> {
    fn tx_packet_header_flags(&self, data: &[u8]) -> PacketHeaderFlags {
        let mut flags = PacketHeaderFlags::empty();

        let Ok(ext) = extract_headers(data) else {
            return flags;
        };

        let capabilities = self.capabilities();

        if matches!(ext.network, NetworkHdr::Ipv4(_)) && !capabilities.checksum.ipv4.tx() {
            flags.insert(PacketHeaderFlags::IPV4_CSUM_OUT); // IPv4 checksum offload
        }

        match ext.transport {
            TransportHdr::Tcp(_) => {
                if !capabilities.checksum.tcp.tx() {
                    flags.insert(PacketHeaderFlags::TCP_CSUM_OUT); // TCP checksum offload
                }
            }
            TransportHdr::Udp(_) => {
                if !capabilities.checksum.udp.tx() {
                    flags.insert(PacketHeaderFlags::UDP_CSUM_OUT); // UDP checksum offload
                }
            }
            _ => {}
        }

        flags
    }
}

impl Device for NetDriverRef<'_> {
    type RxToken<'b>
        = NRxToken
    where
        Self: 'b;
    type TxToken<'b>
        = NTxToken<'b>
    where
        Self: 'b;
    fn capabilities(&self) -> phy::DeviceCapabilities {
        let mut cap = DeviceCapabilities::default();
        cap.max_transmission_unit = 1500;
        cap.max_burst_size = Some(64);

        let capabilities = self.inner.capabilities();

        //if capabilities.contains(NetCapabilities::CSUM_IPv4) {
        //cap.checksum.ipv4 = Checksum::Rx;
        //}

        // Note: Awkernel doen't yet support Ipv6.
        // Additionally, tests for TCP functionality have not yet been conducted.
        // Checksum offload currently only supports UDPv4.

        // if capabilities.contains(NetCapabilities::CSUM_TCPv4 | NetCapabilities::CSUM_TCPv6) {
        //     cap.checksum.tcp = Checksum::Rx;
        // }

        // if capabilities.contains(NetCapabilities::CSUM_UDPv4 | NetCapabilities::CSUM_UDPv6) {
        //     cap.checksum.udp = Checksum::Rx;
        // }

        //if capabilities.contains(NetCapabilities::CSUM_UDPv4) {
        //cap.checksum.udp = Checksum::Rx;
        //}

        cap
    }

    /// The additional transmit token makes it possible to generate a reply packet
    /// based on the contents of the received packet, without heap allocation.
    fn receive(
        &mut self,
        _timestamp: smoltcp::time::Instant,
    ) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        if let Some(que) = self.rx_ringq.as_mut() {
            if let Some(data) = que.pop() {
                return Some((
                    NRxToken { data },
                    NTxToken {
                        tx_ring: self.tx_ringq,
                        driver_ref_inner: self.inner,
                    },
                ));
            }
        }

        None
    }

    /// The real packet transmission is performed when the token is consumed.
    fn transmit(&mut self, _timestamp: smoltcp::time::Instant) -> Option<Self::TxToken<'_>> {
        if !self.inner.can_send() {
            return None;
        }

        if self.tx_ringq.is_full() {
            return None;
        }

        Some(NTxToken {
            tx_ring: self.tx_ringq,
            driver_ref_inner: self.inner,
        })
    }
}

pub(super) struct IfNet {
    vlan: Option<u16>,
    pub(super) inner: Mutex<IfNetInner>,
    pub(super) socket_set: RwLock<SocketSet<'static>>,
    rx_irq_to_driver: BTreeMap<u16, NetDriver>,
    tx_only_ringq: Vec<Mutex<RingQ<(DMAPool<[u8; PAGESIZE]>, usize)>>>,
    pub(super) net_device: Arc<dyn NetDevice + Sync + Send>,
    pub(super) is_poll_mode: bool,
    poll_driver: Option<NetDriver>,
    tick_driver: Option<NetDriver>,
    transmitter: Vec<Mutex<TransmitWakeState>>,
}

pub(super) struct IfNetInner {
    pub(super) interface: Interface,
    pub(super) default_gateway_ipv4: Option<smoltcp::wire::Ipv4Address>,

    multicast_addr_ipv4: BTreeSet<Ipv4Addr>,
    multicast_addr_mac: BTreeMap<[u8; ETHER_ADDR_LEN], u32>,
}

impl IfNetInner {
    #[inline(always)]
    //pub fn split(&mut self) -> (&mut Interface, &mut SocketSet<'static>) {
    //(&mut self.interface, &mut self.socket_set)
    //}

    pub fn get_interface(&mut self) -> &mut Interface {
        &mut self.interface
    }

    #[inline(always)]
    pub fn get_default_gateway_ipv4(&self) -> Option<smoltcp::wire::Ipv4Address> {
        self.default_gateway_ipv4
    }

    #[inline(always)]
    pub fn set_default_gateway_ipv4(&mut self, gateway: smoltcp::wire::Ipv4Address) {
        if self.default_gateway_ipv4.is_some() {
            self.interface.routes_mut().remove_default_ipv4_route();
        }

        self.default_gateway_ipv4 = Some(gateway);
    }
}

fn update_udp_checksum(frame: &mut [u8]) {
    let ip_header_len = ((frame[14] & 0x0F) * 4) as usize;
    let udp_start = 14 + ip_header_len;

    // チェックサムフィールドを0にする
    frame[udp_start + 6] = 0;
    frame[udp_start + 7] = 0;

    let mut sum: u32 = 0;

    // 擬似ヘッダ
    // 送信元IPアドレス (4バイト)
    for i in (26..30).step_by(2) {
        sum += ((frame[i] as u32) << 8 | frame[i + 1] as u32) as u32;
    }
    // 宛先IPアドレス (4バイト)
    for i in (30..34).step_by(2) {
        sum += ((frame[i] as u32) << 8 | frame[i + 1] as u32) as u32;
    }

    // プロトコル (UDP = 17)
    sum += frame[23] as u32;

    // UDPパケット長
    let udp_len = ((frame[udp_start + 4] as u16) << 8 | frame[udp_start + 5] as u16) as u32;
    sum += udp_len;

    // UDPヘッダとデータの処理
    let udp_end = udp_start + udp_len as usize;
    for i in (udp_start..udp_end).step_by(2) {
        if i + 1 < frame.len() {
            sum += ((frame[i] as u32) << 8 | frame[i + 1] as u32) as u32;
        } else {
            sum += (frame[i] as u32) << 8;
        }
    }

    // 上位ビットを折り返して加算
    while (sum >> 16) > 0 {
        sum = (sum & 0xFFFF) + (sum >> 16);
    }

    // 1の補数を取る
    let checksum = !sum as u16;

    // チェックサム 0 は 0xFFFFとして送信
    let checksum = if checksum == 0 { 0xFFFF } else { checksum };

    // チェックサムを挿入
    frame[udp_start + 6] = (checksum >> 8) as u8;
    frame[udp_start + 7] = (checksum & 0xFF) as u8;
}

impl IfNet {
    pub fn new(net_device: Arc<dyn NetDevice + Sync + Send>, vlan: Option<u16>) -> Self {
        let interface = {
            let mut tx_ringq = RingQ::new(0);
            let mut net_driver_ref = NetDriverRef {
                inner: &net_device,
                rx_ringq: None,
                tx_ringq: &mut tx_ringq,
            };

            let instant = Instant::from_micros(crate::delay::uptime() as i64);
            let hardware_address =
                HardwareAddress::Ethernet(smoltcp::wire::EthernetAddress(net_device.mac_address()));
            let mut config = Config::new(hardware_address);
            config.random_seed = crate::delay::uptime();

            Interface::new(config, &mut net_driver_ref, instant)
        };

        let mut transmitter = Vec::new();
        for _ in 0..net_device.num_queues() {
            transmitter.push(Mutex::new(TransmitWakeState::None));
        }

        // Create NetDrivers.
        let mut rx_irq_to_driver = BTreeMap::new();
        let mut tx_only_ringq = Vec::new();

        for irq in net_device.irqs().into_iter() {
            let rx_ringq = RingQ::new(512);

            if let Some(que_id) = net_device.rx_irq_to_que_id(irq) {
                rx_irq_to_driver.insert(
                    irq,
                    NetDriver {
                        inner: net_device.clone(),
                        rx_que_id: que_id,
                        rx_ringq: Mutex::new(rx_ringq),
                    },
                );
            }

            let tx_ringq = Mutex::new(RingQ::new(512));
            tx_only_ringq.push(tx_ringq);
        }

        let poll_driver = if net_device.poll_mode() {
            let tx_ringq = Mutex::new(RingQ::new(512));
            tx_only_ringq.push(tx_ringq);

            Some(NetDriver {
                inner: net_device.clone(),
                rx_que_id: 0,
                rx_ringq: Mutex::new(RingQ::new(512)),
            })
        } else {
            None
        };

        let tick_driver = if net_device.tick_msec().is_some() {
            let tx_ringq = Mutex::new(RingQ::new(512));
            tx_only_ringq.push(tx_ringq);

            Some(NetDriver {
                inner: net_device.clone(),
                rx_que_id: 0,
                rx_ringq: Mutex::new(RingQ::new(512)),
            })
        } else {
            None
        };

        // Create a SocketSet.
        let socket_set = SocketSet::new(vec![]);

        let is_poll_mode = net_device.poll_mode();

        IfNet {
            vlan,
            inner: Mutex::new(IfNetInner {
                interface,
                default_gateway_ipv4: None,
                multicast_addr_ipv4: BTreeSet::new(),
                multicast_addr_mac: BTreeMap::new(),
            }),
            socket_set: RwLock::new(socket_set),
            rx_irq_to_driver,
            net_device,
            tx_only_ringq,
            is_poll_mode,
            poll_driver,
            tick_driver,
            transmitter,
        }
    }

    /// Leave a multicast group.
    /// This function calls `NetDevice::remove_multicast_addr` to remove a multicast address internally.
    ///
    /// Returns `Ok(leave_sent)` if the address was removed successfully,
    /// where `leave_sent` indicates whether an immediate leave packet has been sent.
    pub fn leave_multicast_v4(&self, addr: Ipv4Addr) -> Result<bool, NetManagerError> {
        if !addr.is_multicast() {
            return Err(NetManagerError::MulticastInvalidIpv4Address);
        }

        // Remove the multicast address from the list.
        {
            let mut node = MCSNode::new();
            let inner = self.inner.lock(&mut node);

            if !inner.multicast_addr_ipv4.contains(&addr) {
                return Err(NetManagerError::MulticastNotJoined);
            }
        }

        let mac_addr = ipv4_addr_to_mac_addr(addr);

        // Leave the multicast group.
        self.first_net_driver_ref(move |mut net_driver_ref| {
            let timestamp = Instant::from_micros(crate::delay::uptime() as i64);
            let smoltcp_addr = smoltcp::wire::Ipv4Address::from_bytes(&addr.octets());

            let mut node = MCSNode::new();
            let mut inner = self.inner.lock(&mut node);

            match inner.interface.leave_multicast_group(
                &mut net_driver_ref,
                smoltcp_addr,
                timestamp,
            ) {
                Ok(result) => {
                    inner.multicast_addr_ipv4.remove(&addr);

                    // Disable the multicast address if it is not used.
                    match inner.multicast_addr_mac.entry(mac_addr) {
                        btree_map::Entry::Occupied(mut entry) => {
                            let count = entry.get_mut();

                            if *count == 1 {
                                entry.remove();
                                self.net_device
                                    .remove_multicast_addr(&mac_addr)
                                    .map_err(NetManagerError::DeviceError)?;
                            } else {
                                *count -= 1;
                            }
                        }
                        btree_map::Entry::Vacant(_) => {
                            return Err(NetManagerError::MulticastInvalidIpv4Address);
                        }
                    }

                    Ok(result)
                }
                Err(MulticastError::Exhausted) => Err(NetManagerError::SendError),
                Err(_) => Err(NetManagerError::MulticastError),
            }
        })
    }

    fn first_net_driver_ref<F, T>(&self, mut f: F) -> Result<T, NetManagerError>
    where
        F: FnMut(NetDriverRef) -> Result<T, NetManagerError>,
    {
        let first_driver = self.rx_irq_to_driver.first_key_value();
        let ref_net_driver = first_driver
            .as_ref()
            .ok_or(NetManagerError::InvalidState)?
            .1;

        let tx_ringq = self
            .tx_only_ringq
            .get(ref_net_driver.rx_que_id)
            .ok_or(NetManagerError::InvalidState)?;

        let mut node = MCSNode::new();
        let mut rx_ringq = ref_net_driver.rx_ringq.lock(&mut node);

        let mut node = MCSNode::new();
        let mut tx_ringq = tx_ringq.lock(&mut node);

        let net_driver_ref = NetDriverRef {
            inner: &ref_net_driver.inner,
            rx_ringq: Some(&mut *rx_ringq),
            tx_ringq: &mut tx_ringq,
        };

        f(net_driver_ref)
    }

    /// Join a multicast group.
    /// This function calls `NetDevice::add_multicast_addr` and
    /// `Interface::join_multicast_group` of `smoltcp` to add a multicast address internally.
    ///
    /// Add an address to a list of subscribed multicast IP addresses.
    /// Returns `Ok(announce_sent)`` if the address was added successfully,
    /// where `announce_sent`` indicates whether an initial immediate announcement has been sent.
    pub fn join_multicast_v4(&self, addr: Ipv4Addr) -> Result<bool, NetManagerError> {
        if !addr.is_multicast() {
            return Err(NetManagerError::MulticastInvalidIpv4Address);
        }

        // Enable the multicast address if it is used.
        let mac_addr = ipv4_addr_to_mac_addr(addr);

        {
            // Add the multicast address to the list.
            let mut node = MCSNode::new();
            let mut inner = self.inner.lock(&mut node);

            if inner.multicast_addr_ipv4.contains(&addr) {
                return Ok(false);
            }

            match inner.multicast_addr_mac.entry(mac_addr) {
                btree_map::Entry::Occupied(mut entry) => {
                    *entry.get_mut() += 1;
                }
                btree_map::Entry::Vacant(entry) => {
                    entry.insert(1);
                    self.net_device
                        .add_multicast_addr(&mac_addr)
                        .map_err(NetManagerError::DeviceError)?;
                }
            }
        }

        // Join the multicast group.
        let result = self.first_net_driver_ref(move |mut net_driver_ref| {
            let timestamp = Instant::from_micros(crate::delay::uptime() as i64);
            let smoltcp_addr = smoltcp::wire::Ipv4Address::from_bytes(&addr.octets());

            let mut node = MCSNode::new();
            let mut inner = self.inner.lock(&mut node);

            match inner
                .interface
                .join_multicast_group(&mut net_driver_ref, smoltcp_addr, timestamp)
            {
                Ok(result) => {
                    inner.multicast_addr_ipv4.insert(addr);
                    Ok(result)
                }
                Err(MulticastError::Exhausted) => Err(NetManagerError::SendError),
                Err(_) => Err(NetManagerError::MulticastError),
            }
        });

        if result.is_ok() {
            return result;
        }

        // Error handling.
        // If an error occurs, the multicast address is removed from the list.
        let mut node = MCSNode::new();
        let mut inner = self.inner.lock(&mut node);

        if let btree_map::Entry::Occupied(mut entry) = inner.multicast_addr_mac.entry(mac_addr) {
            let num = entry.get_mut();
            if *num == 1 {
                entry.remove();
                self.net_device
                    .remove_multicast_addr(&mac_addr)
                    .map_err(NetManagerError::DeviceError)?;
            } else {
                *num -= 1;
            }
        }

        result
    }

    pub fn poll_tx_only(&self, que_id: usize) -> bool {
        let Some(tx_ringq) = self.tx_only_ringq.get(que_id) else {
            return false;
        };

        let mut node = MCSNode::new();
        let mut tx_ringq = tx_ringq.lock(&mut node);

        let mut device_ref = NetDriverRef {
            inner: &self.net_device,
            rx_ringq: None,
            tx_ringq: &mut tx_ringq,
        };

        let timestamp = Instant::from_micros(crate::delay::uptime() as i64);

        let result = {
            let mut node = MCSNode::new();
            let mut inner = self.inner.lock(&mut node);

            let interface = inner.get_interface();
            interface.poll(timestamp, &mut device_ref, &self.socket_set)
        };

        let mut count = 0;
        // send packets from the queue.
        while !device_ref.tx_ringq.is_empty() {
            if let Some((data, len)) = device_ref.tx_ringq.pop() {
                let ptr = data.get_virt_addr().as_mut_ptr();
                let slice = unsafe { core::slice::from_raw_parts_mut(ptr as *mut u8, len) };
                let tx_packet_header_flags = device_ref.tx_packet_header_flags(slice);
                //if len > 100 && slice[36] == 78 && slice[37] == 80 {
                //let t = uptime_nano();
                //let bytes = t.to_le_bytes();
                //slice[108..124].copy_from_slice(&bytes);
                //}

                let data = EtherFrameDMAcsum {
                    data,
                    len,
                    vlan: self.vlan,
                    csum_flags: tx_packet_header_flags,
                };
                if self.net_device.push(data, que_id).is_err() {
                    log::error!("Failed to push a packet.");
                }
                //count += 1;
            } else {
                break;
            }
        }

        //let mut node = MCSNode::new();
        //let mut count_vec = COUNT.lock(&mut node);
        //count_vec.push(count);
        //if count_vec.len() == 10000 {
        //if let Some(slice) = count_vec.as_slice().get(100..110) {
        //log::info!("poll_tx_only count:{:?}", slice);
        //}
        //count_vec.clear();
        //}

        drop(device_ref);
        drop(tx_ringq);

        if self.net_device.send(que_id).is_err() {
            log::error!("Failed to send a packet.");
        }

        result
    }

    fn poll_rx(&self, ref_net_driver: &NetDriver) -> bool {
        let que_id = ref_net_driver.rx_que_id;
        let mut node = MCSNode::new();
        let mut rx_ringq = ref_net_driver.rx_ringq.lock(&mut node);

        // receive packets from the RX queue.
        while !rx_ringq.is_full() {
            if let Ok(Some(data)) = ref_net_driver.inner.recv(que_id) {
                //unsafe {
                //let ptr = data.data.get_virt_addr().as_usize() as *mut [u8; PAGESIZE];
                //let len = 142;
                //let data = core::slice::from_raw_parts_mut(ptr as *mut u8, len as usize);
                //if data[36] == 78 && data[37] == 80 {
                //let t = uptime_nano();
                //let bytes = t.to_le_bytes();
                //data[60..76].copy_from_slice(&bytes);
                //update_udp_checksum(data);
                //}
                //}
                let _ = rx_ringq.push(data);
            } else {
                break;
            }
        }

        let Some(tx_ringq) = self.tx_only_ringq.get(que_id) else {
            return false;
        };
        let mut node = MCSNode::new();
        let mut tx_ringq = tx_ringq.lock(&mut node);

        let mut device_ref = NetDriverRef {
            inner: &ref_net_driver.inner,
            rx_ringq: Some(&mut rx_ringq),
            tx_ringq: &mut tx_ringq,
        };

        let result = {
            let timestamp = Instant::from_micros(crate::delay::uptime() as i64);

            let mut node = MCSNode::new();
            let mut inner = self.inner.lock(&mut node);

            let interface = inner.get_interface();

            interface.poll(timestamp, &mut device_ref, &self.socket_set)
        };

        let mut count = 0;
        // send packets from the queue.
        while !device_ref.tx_ringq.is_empty() {
            if let Some((data, len)) = device_ref.tx_ringq.pop() {
                let ptr = data.get_virt_addr().as_mut_ptr();
                let slice = unsafe { core::slice::from_raw_parts_mut(ptr as *mut u8, len) };
                let tx_packet_header_flags = device_ref.tx_packet_header_flags(slice);
                //if len > 100 && slice[36] == 78 && slice[37] == 80 {
                //let t = uptime_nano();
                //let bytes = t.to_le_bytes();
                //slice[108..124].copy_from_slice(&bytes);
                //}

                let data = EtherFrameDMAcsum {
                    data,
                    len,
                    vlan: self.vlan,
                    csum_flags: tx_packet_header_flags,
                };
                if self.net_device.push(data, que_id).is_err() {
                    log::error!("Failed to push a packet.");
                }
                //count += 1;
            } else {
                break;
            }
        }

        //let mut node = MCSNode::new();
        //let mut count_vec = RECV_COUNT.lock(&mut node);
        //count_vec.push(count);
        //if count_vec.len() == 10000 {
        //if let Some(slice) = count_vec.as_slice().get(100..110) {
        //log::info!("poll_rx count:{:?}", slice);
        //}
        //count_vec.clear();
        //}

        let _ = self.net_device.send(que_id);

        result
    }

    #[inline(always)]
    pub fn poll_rx_poll_mode(&self) -> bool {
        let Some(ref_net_driver) = self.poll_driver.as_ref() else {
            return false;
        };

        if ref_net_driver.inner.can_send() {
            self.poll_rx(ref_net_driver)
        } else {
            false
        }
    }

    #[inline(always)]
    pub fn tick_rx_poll_mode(&self) {
        let Some(ref_net_driver) = self.tick_driver.as_ref() else {
            return;
        };

        if ref_net_driver.inner.can_send() {
            self.poll_rx(ref_net_driver);
        }
    }

    /// If some packets are processed, return true.
    /// If poll returns true, the caller should call poll again.
    #[inline(always)]
    pub fn poll_rx_irq(&self, irq: u16) -> bool {
        let Some(ref_net_driver) = self.rx_irq_to_driver.get(&irq) else {
            return false;
        };

        if ref_net_driver.inner.can_send() {
            self.poll_rx(ref_net_driver)
        } else {
            false
        }
    }

    #[inline(always)]
    pub fn wake_transmitter(&self, que_id: usize) {
        let Some(waker) = self.transmitter.get(que_id) else {
            return;
        };

        let mut node = MCSNode::new();
        let mut waker = waker.lock(&mut node);

        let TransmitWakeState::Wake(w) = waker.as_ref() else {
            *waker = TransmitWakeState::Notified;
            return;
        };

        w.wake_by_ref();

        *waker = TransmitWakeState::None;
    }

    /// Returns true if the waker is registered successfully.
    /// Returns false if it is already notified.
    #[inline(always)]
    pub fn register_waker_for_transmitter(
        &self,
        que_id: usize,
        waker: core::task::Waker,
    ) -> Result<bool, NetManagerError> {
        let Some(w) = self.transmitter.get(que_id) else {
            return Err(NetManagerError::InvalidQueueID);
        };

        let mut node = MCSNode::new();
        let mut guard = w.lock(&mut node);

        match guard.as_ref() {
            TransmitWakeState::None => {
                *guard = TransmitWakeState::Wake(waker);
                Ok(true)
            }
            TransmitWakeState::Notified => {
                *guard = TransmitWakeState::None;
                Ok(false)
            }
            TransmitWakeState::Wake(_) => {
                *guard = TransmitWakeState::Wake(waker);
                Ok(true)
            }
        }
    }
}

//pub struct NRxToken {
//data: EtherFrameBuf,
//}

pub struct NRxToken {
    data: EtherFrameDMA,
}

//impl phy::RxToken for NRxToken {
///// Store packet data into the buffer.
///// Closure f will map the raw bytes to the form that
///// could be used in the higher layer of `smoltcp`.
//fn consume<R, F>(mut self, f: F) -> R
//where
//F: FnOnce(&mut [u8]) -> R,
//{
//f(&mut self.data.data)
//}
//}

impl phy::RxToken for NRxToken {
    /// Store packet data into the buffer.
    /// Closure f will map the raw bytes to the form that
    /// could be used in the higher layer of `smoltcp`.
    fn consume<R, F>(mut self, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        f(self.data.data.as_mut())
    }
}

pub struct NTxToken<'a> {
    tx_ring: &'a mut RingQ<(DMAPool<[u8; PAGESIZE]>, usize)>,
    driver_ref_inner: &'a Arc<dyn NetDevice + Sync + Send>,
}

//impl phy::TxToken for NTxToken<'_> {
//fn consume<R, F>(self, len: usize, f: F) -> R
//where
//F: FnOnce(&mut [u8]) -> R,
//{
//let mut buf = Vec::with_capacity(len);

//#[allow(clippy::uninit_vec)]
//unsafe {
//buf.set_len(len);
//};

//let result = f(&mut buf[..len]);

//let _ = self.tx_ring.push(buf);

//result
//}
//}

impl phy::TxToken for NTxToken<'_> {
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        let segment_group = self.driver_ref_inner.get_segment_group().unwrap_or(0);
        let buf: DMAPool<[u8; PAGESIZE]> = DMAPool::new(segment_group as usize, 1).unwrap(); // Not sure this unwrap is acceptable
                                                                                             //log::debug!(
                                                                                             //"phy_addr:{:?} virt_addr:{:?}",
                                                                                             //buf.get_phy_addr(),
                                                                                             //buf.get_virt_addr()
                                                                                             //);

        let ptr = buf.get_virt_addr().as_mut_ptr();
        let slice = unsafe { core::slice::from_raw_parts_mut(ptr as *mut u8, len) };

        let result: R = f(slice);

        let _ = self.tx_ring.push((buf, len));

        result
    }
}
