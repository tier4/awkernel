use crate::net::{ip_addr::IpAddr, NET_MANAGER};
use awkernel_sync::mcs::MCSNode;

use super::NetManagerError;

use alloc::vec;

pub struct UdpSocket {
    handle: smoltcp::iface::SocketHandle,
    interface_id: u64,
    port: u16,
    is_ipv4: bool,
}

impl super::SockUdp for UdpSocket {
    fn bind_on_interface(
        interface_id: u64,
        addr: IpAddr,
        port: Option<u16>,
        rx_buffer_size: usize,
        tx_buffer_size: usize,
    ) -> Result<Self, NetManagerError> {
        let mut net_manager = NET_MANAGER.write();

        let is_ipv4;
        let port = if let Some(port) = port {
            if port == 0 {
                return Err(NetManagerError::InvalidPort);
            }

            // Check if the specified port is available.
            if addr.is_ipv4() {
                if net_manager.is_port_in_use_udp_ipv4(port) {
                    return Err(NetManagerError::PortInUse);
                }

                is_ipv4 = true;
                net_manager.set_port_in_use_udp_ipv4(port);
                port
            } else {
                if net_manager.is_port_in_use_udp_ipv6(port) {
                    return Err(NetManagerError::PortInUse);
                }

                is_ipv4 = false;
                net_manager.set_port_in_use_udp_ipv6(port);
                port
            }
        } else {
            // Find an ephemeral port.
            if addr.is_ipv4() {
                is_ipv4 = true;
                net_manager
                    .get_ephemeral_port_udp_ipv4()
                    .ok_or(NetManagerError::PortInUse)?
            } else {
                is_ipv4 = false;
                net_manager
                    .get_ephemeral_port_udp_ipv6()
                    .ok_or(NetManagerError::PortInUse)?
            }
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
            vec![0; rx_buffer_size],
        );
        let udp_tx_buffer = udp::PacketBuffer::new(
            vec![udp::PacketMetadata::EMPTY, udp::PacketMetadata::EMPTY],
            vec![0; tx_buffer_size],
        );

        let mut socket = udp::Socket::new(udp_rx_buffer, udp_tx_buffer);

        // Bind the socket to the specified port.
        match addr.addr {
            smoltcp::wire::IpAddress::Ipv4(addr) => {
                if addr.is_unspecified() {
                    // Bind to any address.
                    socket.bind(port).expect("udp socket bind");
                } else {
                    socket.bind((addr, port)).expect("udp socket bind");
                }
            }
            smoltcp::wire::IpAddress::Ipv6(addr) => {
                if addr.is_unspecified() {
                    // Bind to any address.
                    socket.bind(port).expect("udp socket bind");
                } else {
                    socket.bind((addr, port)).expect("udp socket bind");
                }
            }
        }

        // Add the socket to the interface.
        let handle = if_net.socket_set.write().add(socket);

        Ok(UdpSocket {
            handle,
            interface_id,
            port,
            is_ipv4,
        })
    }

    fn send_to(
        &self,
        buf: &[u8],
        addr: &IpAddr,
        port: u16,
        waker: &core::task::Waker,
    ) -> Result<bool, NetManagerError> {
        let net_manager = NET_MANAGER.read();

        let Some(if_net) = net_manager.interfaces.get(&self.interface_id) else {
            return Err(NetManagerError::InvalidInterfaceID);
        };

        if !if_net.net_device.can_send() {
            return Err(NetManagerError::InterfaceIsNotReady);
        }

        let if_net = if_net.clone();
        drop(net_manager);

        let socket_set = if_net.socket_set.read();
        let socket_mutex = socket_set.get::<smoltcp::socket::udp::Socket>(self.handle);

        let mut node = MCSNode::new();
        let mut socket = socket_mutex.lock(&mut node);

        let can_send = socket.can_send();
        if can_send {
            socket
                .send_slice(buf, (addr.addr, port))
                .or(Err(NetManagerError::SendError))?;

            let que_id = crate::cpu::raw_cpu_id() & (if_net.net_device.num_queues() - 1);

            // To avoid deadlock
            drop(socket);
            drop(socket_set);
            if_net.poll_tx_only(que_id);

            Ok(true)
        } else {
            socket.register_send_waker(waker);
            Ok(false)
        }
    }

    fn recv(
        &self,
        buf: &mut [u8],
        waker: &core::task::Waker,
    ) -> Result<Option<(usize, IpAddr, u16)>, NetManagerError> {
        let net_manager = NET_MANAGER.read();

        let Some(if_net) = net_manager.interfaces.get(&self.interface_id) else {
            return Err(NetManagerError::InvalidInterfaceID);
        };

        let if_net = if_net.clone();
        drop(net_manager);

        let socket_set = if_net.socket_set.read();
        let socket_mutex = socket_set.get::<smoltcp::socket::udp::Socket>(self.handle);

        let mut node = MCSNode::new();
        let mut socket = socket_mutex.lock(&mut node);
        if socket.can_recv() {
            let (data, meta_data) = socket.recv().or(Err(NetManagerError::RecvError))?;

            let len = buf.len().min(data.len());

            unsafe { core::ptr::copy_nonoverlapping(data.as_ptr(), buf.as_mut_ptr(), len) };

            Ok(Some((
                len,
                IpAddr {
                    addr: meta_data.endpoint.addr,
                },
                meta_data.endpoint.port,
            )))
        } else {
            socket.register_recv_waker(waker);
            Ok(None)
        }
    }
}

impl Drop for UdpSocket {
    fn drop(&mut self) {
        let mut net_manager = NET_MANAGER.write();

        if self.is_ipv4 {
            net_manager.free_port_udp_ipv4(self.port);
        } else {
            net_manager.free_port_udp_ipv6(self.port);
        }

        if let Some(if_net) = net_manager.interfaces.get(&self.interface_id) {
            if_net.socket_set.write().remove(self.handle);
        }
    }
}
