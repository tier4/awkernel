use crate::{net::NET_MANAGER, sync::mcs::MCSNode};

use super::NetManagerError;

use alloc::{vec, vec::Vec};

use core::net::IpAddr;

pub struct UdpSocket {
    handle: smoltcp::iface::SocketHandle,
    interface_id: u64,
    port: u16,
}

impl UdpSocket {
    /// Create a UDP socket for IPv4.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_lib::net::socket::UDPSocket;
    ///
    /// fn example_udp_socket_ipv4() {
    ///     let handler = UDPSocket::create_ipv4_on_iface("0.0.0.0", 10000, 0, 64 * 1024).unwrap();
    /// }
    /// ```
    pub fn create_ipv4_on_iface(
        interface_id: u64,
        port: u16,
        buffer_size: usize,
    ) -> Result<Self, NetManagerError> {
        let mut net_manager = NET_MANAGER.write();

        let port = if port == 0 {
            // Find an ephemeral port.
            let mut ephemeral_port = None;
            for i in 0..(u16::MAX >> 2) {
                let port = net_manager.udp_port_ipv4_ephemeral.wrapping_add(i);
                let port = if port == 0 { u16::MAX >> 2 } else { port };

                if !net_manager.udp_ports_ipv4.contains(&port) {
                    net_manager.udp_ports_ipv4.insert(port);
                    net_manager.udp_port_ipv4_ephemeral = port;
                    ephemeral_port = Some(port);
                    break;
                }
            }

            if let Some(port) = ephemeral_port {
                port
            } else {
                return Err(NetManagerError::PortInUse);
            }
        } else {
            // Check if the specified port is available.
            if net_manager.udp_ports_ipv4.contains(&port) {
                return Err(NetManagerError::PortInUse);
            }

            net_manager.udp_ports_ipv4.insert(port);
            port
        };

        // Find the interface that has the specified address.
        let if_net = net_manager
            .interfaces
            .get(&interface_id)
            .ok_or(NetManagerError::InvalidInterfaceID)?
            .clone();

        drop(net_manager);

        // Create a UDP socket.
        use smoltcp::socket::udp;
        let udp_rx_buffer = udp::PacketBuffer::new(
            vec![udp::PacketMetadata::EMPTY, udp::PacketMetadata::EMPTY],
            vec![0; buffer_size],
        );
        let udp_tx_buffer = udp::PacketBuffer::new(
            vec![udp::PacketMetadata::EMPTY, udp::PacketMetadata::EMPTY],
            vec![0; buffer_size],
        );

        let mut socket = udp::Socket::new(udp_rx_buffer, udp_tx_buffer);

        // Bind the socket to the specified port.
        socket.bind(port).expect("udp socket bind");

        // Add the socket to the interface.
        let handle = {
            let mut node = MCSNode::new();
            let mut if_net_inner = if_net.inner.lock(&mut node);

            if_net_inner.socket_set.add(socket)
        };

        Ok(UdpSocket {
            handle,
            interface_id,
            port,
        })
    }

    /// Send a UDP packet to the specified address and port.
    /// If the packet is sent successfully, true is returned.
    /// If the packet is not sent because the socket is not ready, false is returned,
    /// and the waker is registered for the socket.
    pub fn sendto(
        &self,
        data: &[u8],
        addr: &IpAddr,
        port: u16,
        waker: &core::task::Waker,
    ) -> Result<bool, NetManagerError> {
        let net_manager = NET_MANAGER.read();

        let Some(if_net) = net_manager.interfaces.get(&self.interface_id) else {
        return Err(NetManagerError::InvalidInterfaceID);
    };

        let addr = match addr {
            IpAddr::V6(addr) => {
                let octets = addr.octets();
                smoltcp::wire::IpAddress::v6(
                    ((octets[1] as u16) << 8) | octets[0] as u16,
                    ((octets[3] as u16) << 8) | octets[2] as u16,
                    ((octets[5] as u16) << 8) | octets[4] as u16,
                    ((octets[7] as u16) << 8) | octets[6] as u16,
                    ((octets[9] as u16) << 8) | octets[8] as u16,
                    ((octets[11] as u16) << 8) | octets[10] as u16,
                    ((octets[13] as u16) << 8) | octets[12] as u16,
                    ((octets[15] as u16) << 8) | octets[14] as u16,
                )
            }
            IpAddr::V4(addr) => {
                let octets = addr.octets();
                smoltcp::wire::IpAddress::v4(octets[0], octets[1], octets[2], octets[3])
            }
        };

        let mut node = MCSNode::new();
        let mut inner = if_net.inner.lock(&mut node);

        let socket = inner
            .socket_set
            .get_mut::<smoltcp::socket::udp::Socket>(self.handle);

        if socket.can_send() {
            socket
                .send_slice(data, (addr, port))
                .or(Err(NetManagerError::SendError))?;
            Ok(true)
        } else {
            socket.register_send_waker(waker);
            Ok(false)
        }
    }

    /// Receive a UDP packet.
    /// If a packet is received, the data, source address, and source port are returned.
    /// If a packet is not received, an error is returned.
    /// If the socket is not ready to receive, the waker is registered for the socket.
    pub fn recv(
        &self,
        waker: &core::task::Waker,
    ) -> Result<Option<(Vec<u8>, IpAddr, u16)>, NetManagerError> {
        let net_manager = NET_MANAGER.read();

        let Some(if_net) = net_manager.interfaces.get(&self.interface_id) else {
            return Err(NetManagerError::InvalidInterfaceID);
        };

        let mut node = MCSNode::new();
        let mut inner = if_net.inner.lock(&mut node);

        let socket = inner
            .socket_set
            .get_mut::<smoltcp::socket::udp::Socket>(self.handle);

        if socket.can_recv() {
            let (data, meta_data) = socket.recv().or(Err(NetManagerError::RecvError))?;

            let (addr, port) = match meta_data.endpoint.addr {
                smoltcp::wire::IpAddress::Ipv4(addr) => {
                    let addr = IpAddr::V4(core::net::Ipv4Addr::new(
                        addr.0[0], addr.0[1], addr.0[2], addr.0[3],
                    ));
                    let port = meta_data.endpoint.port;
                    (addr, port)
                }
                smoltcp::wire::IpAddress::Ipv6(addr) => {
                    let addr = IpAddr::V6(core::net::Ipv6Addr::new(
                        ((addr.0[1] as u16) << 8) | addr.0[0] as u16,
                        ((addr.0[3] as u16) << 8) | addr.0[2] as u16,
                        ((addr.0[5] as u16) << 8) | addr.0[4] as u16,
                        ((addr.0[7] as u16) << 8) | addr.0[6] as u16,
                        ((addr.0[9] as u16) << 8) | addr.0[8] as u16,
                        ((addr.0[11] as u16) << 8) | addr.0[10] as u16,
                        ((addr.0[13] as u16) << 8) | addr.0[12] as u16,
                        ((addr.0[15] as u16) << 8) | addr.0[14] as u16,
                    ));
                    let port = meta_data.endpoint.port;
                    (addr, port)
                }
            };

            Ok(Some((data.to_vec(), addr, port)))
        } else {
            socket.register_recv_waker(waker);
            Ok(None)
        }
    }
}

impl Drop for UdpSocket {
    fn drop(&mut self) {
        let mut net_manager = NET_MANAGER.write();
        net_manager.udp_ports_ipv4.remove(&self.port);

        if let Some(if_net) = net_manager.interfaces.get(&self.interface_id) {
            let mut node = MCSNode::new();
            let mut if_net_inner = if_net.inner.lock(&mut node);
            if_net_inner.socket_set.remove(self.handle);
        }
    }
}
