use alloc::collections::{btree_map::Entry, BTreeMap, VecDeque};
use smoltcp::iface::SocketHandle;

use crate::sync::{mcs::MCSNode, mutex::Mutex};

use super::{tcp::TcpPort, NET_MANAGER};

static CLOSED_CONNECTIONS: Mutex<BTreeMap<u64, VecDeque<(SocketHandle, TcpPort)>>> =
    Mutex::new(BTreeMap::new());

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TcpResult {
    Ok(usize),
    WouldBlock,
    CloseLocal,
    CloseRemote,
    Unreachable,
    InvalidState,
}

pub struct TcpStream {
    pub(super) handle: smoltcp::iface::SocketHandle,
    pub(super) interface_id: u64,
    pub(super) port: Option<TcpPort>,
}

impl Drop for TcpStream {
    fn drop(&mut self) {
        let net_manager = NET_MANAGER.read();

        let Some(if_net) = net_manager
            .interfaces
            .get(&self.interface_id) else {
            return;
        };

        let if_net = if_net.clone();

        drop(net_manager);

        {
            let mut node = MCSNode::new();
            let mut inner = if_net.inner.lock(&mut node);

            let socket: &mut smoltcp::socket::tcp::Socket = inner.socket_set.get_mut(self.handle);

            // If the socket is already closed, remove it from the socket set.
            if matches!(socket.state(), smoltcp::socket::tcp::State::Closed) {
                inner.socket_set.remove(self.handle);

                return;
            }

            // Otherwise, close the socket.
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

/// Close all connections that are in the closed state.
/// This function should be called periodically to clean up closed connections.
pub fn close_connections() {
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
                let mut node = MCSNode::new();
                let mut inner = if_net.inner.lock(&mut node);

                while let Some((handle, port)) = v.pop_front() {
                    let socket: &mut smoltcp::socket::tcp::Socket =
                        inner.socket_set.get_mut(handle);
                    if socket.state() == smoltcp::socket::tcp::State::Closed {
                        // If the socket is already closed, remove it from the socket set.
                        inner.socket_set.remove(handle);
                    } else {
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

impl TcpStream {
    /// Send a TCP packet.
    ///
    /// - If the packet is sent successfully, the number of bytes sent is returned.
    /// - If the packet is not sent because the socket is not ready, TcpResult::WouldBlock is returned,
    ///   and the waker is registered for the socket.
    /// - If the packet is not sent because the socket is half-closed locally, TcpResult::CloseLocal is returned.
    /// - If the packet is not sent because the socket is invalid, TcpResult::InvalidState is returned.
    /// - If the interface is unreachable, TcpResult::Unreachable is returned.
    pub fn send(&mut self, buf: &[u8], waker: &core::task::Waker) -> TcpResult {
        let net_manager = NET_MANAGER.read();

        let Some(if_net) = net_manager
            .interfaces
            .get(&self.interface_id) else {
            return TcpResult::Unreachable;
        };

        let if_net = if_net.clone();
        drop(net_manager);

        let mut node = MCSNode::new();
        let mut inner = if_net.inner.lock(&mut node);

        let socket: &mut smoltcp::socket::tcp::Socket = inner.socket_set.get_mut(self.handle);

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
    pub fn recv(&mut self, buf: &mut [u8], waker: &core::task::Waker) -> TcpResult {
        let net_manager = NET_MANAGER.read();

        let Some(if_net) = net_manager
            .interfaces
            .get(&self.interface_id) else {
            return TcpResult::Unreachable;
        };

        let if_net = if_net.clone();
        drop(net_manager);

        let mut node = MCSNode::new();
        let mut inner = if_net.inner.lock(&mut node);

        let socket: &mut smoltcp::socket::tcp::Socket = inner.socket_set.get_mut(self.handle);

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
}
