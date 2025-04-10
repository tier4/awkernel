use crate::net::{ip_addr::IpAddr, tcp::TcpPort, NetManagerError, NET_MANAGER};

use super::{SockTcpStream, TcpResult};

use alloc::{
    collections::{btree_map::Entry, BTreeMap, VecDeque},
    vec,
};

use crate::sync::{mcs::MCSNode, mutex::Mutex};

use smoltcp::iface::SocketHandle;

static CLOSED_CONNECTIONS: Mutex<BTreeMap<u64, VecDeque<(SocketHandle, TcpPort)>>> =
    Mutex::new(BTreeMap::new());

pub struct TcpStream {
    pub(crate) handle: smoltcp::iface::SocketHandle,
    pub(crate) interface_id: u64,
    pub(crate) port: Option<TcpPort>,
}

impl Drop for TcpStream {
    fn drop(&mut self) {
        let net_manager = NET_MANAGER.read();

        let Some(if_net) = net_manager.interfaces.get(&self.interface_id) else {
            return;
        };

        let if_net = if_net.clone();

        drop(net_manager);

        {
            let socket_set = if_net.socket_set.read();
            let closed = {
                let mut node: MCSNode<smoltcp::socket::tcp::Socket> = MCSNode::new();
                let socket = socket_set
                    .get::<smoltcp::socket::tcp::Socket>(self.handle)
                    .lock(&mut node);

                matches!(socket.state(), smoltcp::socket::tcp::State::Closed)
            };

            // If the socket is already closed, remove it from the socket set.
            if closed {
                drop(socket_set);
                let mut socket_set = if_net.socket_set.write();
                socket_set.remove(self.handle);
                return;
            }

            // Otherwise, close the socket.
            let mut node: MCSNode<smoltcp::socket::tcp::Socket> = MCSNode::new();
            let mut socket = socket_set
                .get::<smoltcp::socket::tcp::Socket>(self.handle)
                .lock(&mut node);
            socket.close();
        }

        let que_id = crate::cpu::raw_cpu_id() & (if_net.net_device.num_queues() - 1);
        if_net.poll_tx_only(que_id);

        let mut node = MCSNode::new();
        let mut closed_connections = CLOSED_CONNECTIONS.lock(&mut node);

        let entry = closed_connections.entry(self.interface_id);
        match entry {
            Entry::Occupied(mut entry) => {
                entry
                    .get_mut()
                    .push_back((self.handle, self.port.take().unwrap()));
            }
            Entry::Vacant(entry) => {
                let mut v = VecDeque::new();
                v.push_back((self.handle, self.port.take().unwrap()));
                entry.insert(v);
            }
        }
    }
}

impl SockTcpStream for TcpStream {
    fn connect(
        interface_id: u64,
        remote_addr: &IpAddr,
        remote_port: u16,
        rx_buffer_size: usize,
        tx_buffer_size: usize,
        waker: &core::task::Waker,
    ) -> Result<TcpStream, NetManagerError> {
        let mut net_manager = NET_MANAGER.write();

        let if_net = net_manager
            .interfaces
            .get(&interface_id)
            .ok_or(NetManagerError::InvalidInterfaceID)?;
        let if_net = if_net.clone();

        let local_port = if remote_addr.is_ipv4() {
            net_manager
                .get_ephemeral_port_tcp_ipv4()
                .ok_or(NetManagerError::NoAvailablePort)?
        } else {
            net_manager
                .get_ephemeral_port_tcp_ipv6()
                .ok_or(NetManagerError::NoAvailablePort)?
        };

        drop(net_manager);

        let rx_buffer = smoltcp::socket::tcp::SocketBuffer::new(vec![0; rx_buffer_size]);
        let tx_buffer = smoltcp::socket::tcp::SocketBuffer::new(vec![0; tx_buffer_size]);

        let socket = smoltcp::socket::tcp::Socket::new(rx_buffer, tx_buffer);

        let handle;
        {
            let mut node = MCSNode::new();
            let mut inner = if_net.inner.lock(&mut node);

            let interface = inner.get_interface();

            let mut socket_set = if_net.socket_set.write();
            handle = socket_set.add(socket);

            let connect_is_err = {
                let mut node: MCSNode<smoltcp::socket::tcp::Socket> = MCSNode::new();
                let mut socket = socket_set
                    .get::<smoltcp::socket::tcp::Socket>(handle)
                    .lock(&mut node);

                socket.register_send_waker(waker);

                socket
                    .connect(
                        interface.context(),
                        (remote_addr.addr, remote_port),
                        local_port.port(),
                    )
                    .is_err()
            };

            if connect_is_err {
                socket_set.remove(handle);
                return Err(NetManagerError::InvalidState);
            }
        }

        let que_id = crate::cpu::raw_cpu_id() & (if_net.net_device.num_queues() - 1);
        if_net.poll_tx_only(que_id);

        Ok(TcpStream {
            handle,
            interface_id,
            port: Some(local_port),
        })
    }

    /// Send a TCP packet.
    ///
    /// - If the packet is sent successfully, the number of bytes sent is returned.
    /// - If the packet is not sent because the socket is not ready, TcpResult::WouldBlock is returned,
    ///   and the waker is registered for the socket.
    /// - If the packet is not sent because the socket is half-closed locally, TcpResult::CloseLocal is returned.
    /// - If the packet is not sent because the socket is invalid, TcpResult::InvalidState is returned.
    /// - If the interface is unreachable, TcpResult::Unreachable is returned.
    fn send(&mut self, buf: &[u8], waker: &core::task::Waker) -> TcpResult {
        let net_manager = NET_MANAGER.read();

        let Some(if_net) = net_manager.interfaces.get(&self.interface_id) else {
            return TcpResult::Unreachable;
        };

        let if_net = if_net.clone();
        drop(net_manager);

        let socket_set = if_net.socket_set.read();

        let mut node: MCSNode<smoltcp::socket::tcp::Socket> = MCSNode::new();
        let mut socket = socket_set
            .get::<smoltcp::socket::tcp::Socket>(self.handle)
            .lock(&mut node);

        if socket.state() == smoltcp::socket::tcp::State::SynSent {
            socket.register_recv_waker(waker);
            return TcpResult::WouldBlock;
        }

        if !socket.may_send() {
            return TcpResult::CloseLocal;
        }

        if !socket.can_send() {
            socket.register_send_waker(waker);
            return TcpResult::WouldBlock;
        }

        let Ok(len) = socket.send_slice(buf) else {
            return TcpResult::InvalidState;
        };

        TcpResult::Ok(len)
    }

    /// Receive a TCP packet.
    ///
    /// - If the packet is received successfully, the number of bytes received is returned.
    /// - If the packet is not received because the socket is not ready, TcpResult::WouldBlock is returned,
    ///   and the waker is registered for the socket.
    /// - If the packet is not received because the socket is half-closed remotely, TcpResult::CloseRemote is returned.
    /// - If the packet is not received because the socket is invalid, TcpResult::InvalidState is returned.
    /// - If the interface is unreachable, TcpResult::Unreachable is returned.
    fn recv(&mut self, buf: &mut [u8], waker: &core::task::Waker) -> TcpResult {
        let net_manager = NET_MANAGER.read();

        let Some(if_net) = net_manager.interfaces.get(&self.interface_id) else {
            return TcpResult::Unreachable;
        };

        let if_net = if_net.clone();
        drop(net_manager);

        let socket_set = if_net.socket_set.read();

        let mut node: MCSNode<smoltcp::socket::tcp::Socket> = MCSNode::new();
        let mut socket = socket_set
            .get::<smoltcp::socket::tcp::Socket>(self.handle)
            .lock(&mut node);

        if socket.state() == smoltcp::socket::tcp::State::SynSent {
            socket.register_recv_waker(waker);
            return TcpResult::WouldBlock;
        }

        if !socket.may_recv() {
            return TcpResult::CloseRemote;
        }

        if !socket.can_recv() {
            socket.register_recv_waker(waker);
            return TcpResult::WouldBlock;
        }

        let Ok(len) = socket.recv_slice(buf) else {
            return TcpResult::InvalidState;
        };

        TcpResult::Ok(len)
    }

    fn remote_addr(&self) -> Result<(IpAddr, u16), NetManagerError> {
        let net_manager = NET_MANAGER.read();

        let if_net = net_manager
            .interfaces
            .get(&self.interface_id)
            .ok_or(NetManagerError::InvalidInterfaceID)?;

        let if_net = if_net.clone();
        drop(net_manager);

        let socket_set = if_net.socket_set.read();

        let mut node: MCSNode<smoltcp::socket::tcp::Socket> = MCSNode::new();
        let socket = socket_set
            .get::<smoltcp::socket::tcp::Socket>(self.handle)
            .lock(&mut node);

        if let Some(endpoint) = socket.remote_endpoint() {
            Ok((
                IpAddr {
                    addr: endpoint.addr,
                },
                endpoint.port,
            ))
        } else {
            Err(NetManagerError::InvalidState)
        }
    }
}

/// Close all connections that are in the closed state.
/// This function should be called periodically to clean up closed connections.
pub(super) fn close_connections() {
    let mut remain = BTreeMap::new();

    let mut node = MCSNode::new();
    let mut closed_connections = CLOSED_CONNECTIONS.lock(&mut node);

    for (interface_id, v) in closed_connections.iter_mut() {
        let net_manager = NET_MANAGER.read();

        if let Some(if_net) = net_manager.interfaces.get(interface_id) {
            let if_net = if_net.clone();
            drop(net_manager);

            // TCP connections which are not closed yet.
            let mut remain_v = VecDeque::new();

            {
                while let Some((handle, port)) = v.pop_front() {
                    let socket_set = if_net.socket_set.read();
                    let closed = {
                        let mut node: MCSNode<smoltcp::socket::tcp::Socket> = MCSNode::new();
                        let socket = socket_set
                            .get::<smoltcp::socket::tcp::Socket>(handle)
                            .lock(&mut node);
                        socket.state() == smoltcp::socket::tcp::State::Closed
                    };
                    if closed {
                        drop(socket_set);
                        let mut socket_set = if_net.socket_set.write();
                        // If the socket is already closed, remove it from the socket set.
                        socket_set.remove(handle);
                    } else {
                        let mut node: MCSNode<smoltcp::socket::tcp::Socket> = MCSNode::new();
                        let mut socket = socket_set
                            .get::<smoltcp::socket::tcp::Socket>(handle)
                            .lock(&mut node);
                        socket.close();
                        remain_v.push_back((handle, port));
                    }
                }
            }

            if_net.poll_tx_only(crate::cpu::raw_cpu_id() & (if_net.net_device.num_queues() - 1));

            remain.insert(*interface_id, remain_v);
        }
    }

    *closed_connections = remain;
}
