use alloc::{collections::VecDeque, vec, vec::Vec};
use smoltcp::iface::SocketHandle;

use crate::sync::mcs::MCSNode;

use super::{ip_addr::IpAddr, tcp_stream::TcpStream, NetManagerError, NET_MANAGER};

pub struct TcpListener {
    handles: Vec<SocketHandle>,
    connected_sockets: VecDeque<SocketHandle>,
    interface_id: u64,
    addr: IpAddr,
    port: u16,
    buffer_size: usize,
}

impl TcpListener {
    pub fn bind_on_interface(
        interface_id: u64,
        addr: IpAddr,
        port: u16,
        buffer_size: usize,
        num_waiting_connections: usize,
    ) -> Result<TcpListener, NetManagerError> {
        let mut net_manager = NET_MANAGER.write();

        let port = if port == 0 {
            // Find an ephemeral port.
            let mut ephemeral_port = None;
            for i in 0..(u16::MAX >> 2) {
                let port = net_manager.tcp_port_ipv4_ephemeral.wrapping_add(i);
                let port = if port == 0 { u16::MAX >> 2 } else { port };

                if !net_manager.tcp_listen_ports_ipv4.contains(&port) {
                    net_manager.tcp_listen_ports_ipv4.insert(port);
                    net_manager.tcp_port_ipv4_ephemeral = port;
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
            if net_manager.tcp_listen_ports_ipv4.contains(&port) {
                return Err(NetManagerError::PortInUse);
            }

            net_manager.tcp_listen_ports_ipv4.insert(port);
            port
        };

        // Find the interface that has the specified address.
        let if_net = net_manager
            .interfaces
            .get(&interface_id)
            .ok_or(NetManagerError::InvalidInterfaceID)?
            .clone();

        drop(net_manager);

        let mut handles = Vec::new();

        for _ in 0..num_waiting_connections {
            // Create a TCP socket.
            let socket = create_listen_socket(&addr, port, buffer_size);

            let handle = {
                let mut node = MCSNode::new();
                let mut if_net_inner = if_net.inner.lock(&mut node);

                if_net_inner.socket_set.add(socket)
            };

            handles.push(handle);
        }

        Ok(TcpListener {
            handles,
            connected_sockets: VecDeque::new(),
            interface_id,
            addr,
            port,
            buffer_size,
        })
    }

    pub fn accept(
        &mut self,
        waker: &core::task::Waker,
    ) -> Result<Option<TcpStream>, NetManagerError> {
        // If there is a connected socket, return it.
        if let Some(handle) = self.connected_sockets.pop_front() {
            return Ok(Some(TcpStream {
                handle,
                interface_id: self.interface_id,
            }));
        }

        let net_manager = NET_MANAGER.read();

        let if_net = net_manager
            .interfaces
            .get(&self.interface_id)
            .ok_or(NetManagerError::InvalidInterfaceID)?;

        let if_net = if_net.clone();
        drop(net_manager);

        let mut node = MCSNode::new();
        let mut interface = if_net.inner.lock(&mut node);

        for handle in self.handles.iter_mut() {
            let socket: &smoltcp::socket::tcp::Socket = interface.socket_set.get(*handle);
            if socket.is_active() {
                // If the socket is active, create a new socket and add it to the interface.
                let new_socket = create_listen_socket(&self.addr, self.port, self.buffer_size);
                let mut new_handle = interface.socket_set.add(new_socket);

                // Swap the new handle with the old handle.
                core::mem::swap(handle, &mut new_handle);

                // The old handle is now a connected socket.
                self.connected_sockets.push_back(new_handle);
            } else if !socket.is_open() {
                // If the socket is not open, create a new socket and add it to the interface.
                let new_socket = create_listen_socket(&self.addr, self.port, self.buffer_size);
                interface.socket_set.remove(*handle);
                *handle = interface.socket_set.add(new_socket);
            }
        }

        // If there is a connected socket, return it.
        if let Some(handle) = self.connected_sockets.pop_front() {
            return Ok(Some(TcpStream {
                handle,
                interface_id: self.interface_id,
            }));
        }

        // Register the waker for the listening sockets.
        for handle in self.handles.iter() {
            let socket: &mut smoltcp::socket::tcp::Socket = interface.socket_set.get_mut(*handle);
            socket.register_recv_waker(waker);
        }

        Ok(None)
    }
}

impl Drop for TcpListener {
    fn drop(&mut self) {
        let mut net_manager = NET_MANAGER.write();
        net_manager.tcp_listen_ports_ipv4.remove(&self.port);

        if let Some(if_net) = net_manager.interfaces.get(&self.interface_id) {
            let if_net = if_net.clone();
            drop(net_manager);

            let mut node = MCSNode::new();
            let mut inner = if_net.inner.lock(&mut node);

            // Close listening sockets.
            for handle in self.handles.iter() {
                let socket: &mut smoltcp::socket::tcp::Socket = inner.socket_set.get_mut(*handle);
                socket.abort();
            }

            // Close connected sockets.
            for handle in self.connected_sockets.iter() {
                let socket: &mut smoltcp::socket::tcp::Socket = inner.socket_set.get_mut(*handle);
                socket.abort();
            }

            drop(inner);

            let que_id = crate::cpu::raw_cpu_id() & (if_net.net_device.num_queues() - 1);
            if_net.poll_tx_only(que_id);
        }
    }
}

fn create_listen_socket(
    addr: &IpAddr,
    port: u16,
    buffer_size: usize,
) -> smoltcp::socket::tcp::Socket<'static> {
    // Create a TCP socket.
    let rx_buffer = smoltcp::socket::tcp::SocketBuffer::new(vec![0; buffer_size]);
    let tx_buffer = smoltcp::socket::tcp::SocketBuffer::new(vec![0; buffer_size]);

    let mut socket = smoltcp::socket::tcp::Socket::new(rx_buffer, tx_buffer);

    // Bind the socket to the address and port.
    match addr.addr {
        smoltcp::wire::IpAddress::Ipv4(addr) => {
            if addr.is_unspecified() {
                socket.listen(port).expect("tcp listen");
            } else {
                socket.listen((addr, port)).expect("tcp listen");
            }
        }
        smoltcp::wire::IpAddress::Ipv6(addr) => {
            if addr.is_unspecified() {
                socket.listen(port).expect("tcp listen");
            } else {
                socket.listen((addr, port)).expect("tcp listen");
            }
        }
    }

    socket
}
