use alloc::collections::{btree_map::Entry, BTreeMap, VecDeque};
use smoltcp::iface::SocketHandle;

use crate::sync::{mcs::MCSNode, mutex::Mutex};

use super::{tcp::TcpPort, NET_MANAGER};

static CLOSED_CONNECTIONS: Mutex<BTreeMap<u64, VecDeque<(SocketHandle, TcpPort)>>> =
    Mutex::new(BTreeMap::new());

pub struct TcpStream {
    pub(super) handle: smoltcp::iface::SocketHandle,
    pub(super) interface_id: u64,
    pub(super) port: Option<TcpPort>,
}

impl Drop for TcpStream {
    fn drop(&mut self) {
        log::debug!("drop TcpStream");
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
                log::debug!("drop TcpStream: state is Closed");
                inner.socket_set.remove(self.handle);

                return;
            }

            // Otherwise, close the socket.
            log::debug!("drop TcpStream: close socket: state = {:?}", socket.state());
            socket.close();
        }

        let que_id = crate::cpu::raw_cpu_id() & (if_net.net_device.num_queues() - 1);
        log::debug!("drop TcpStream: poll_tx_only({})", que_id);
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

        log::debug!("drop TcpStream end");
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

            let mut remain_v = VecDeque::new();

            {
                let mut node = MCSNode::new();
                let mut inner = if_net.inner.lock(&mut node);

                while let Some((handle, port)) = v.pop_front() {
                    let socket: &mut smoltcp::socket::tcp::Socket =
                        inner.socket_set.get_mut(handle);
                    if !matches!(socket.state(), smoltcp::socket::tcp::State::Closed) {
                        socket.close();
                        remain_v.push_back((handle, port));
                    } else {
                        log::debug!("drop TcpStream: state is Closed");
                        inner.socket_set.remove(handle);
                    }
                }
            }

            if_net.poll_tx_only(crate::cpu::raw_cpu_id() & (if_net.net_device.num_queues() - 1));

            remain.insert(*interface_id, remain_v);
        }
    }

    *closed_connections = remain;

    drop(closed_connections);
}
