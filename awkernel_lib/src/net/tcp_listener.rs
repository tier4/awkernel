use alloc::vec;

use crate::sync::mcs::MCSNode;

use super::{ip_addr::IpAddr, NetManagerError, NET_MANAGER};

pub struct TcpListener {
    handle: smoltcp::iface::SocketHandle,
    interface_id: u64,
}

impl TcpListener {
    pub fn bind_on_interface(
        interface_id: u64,
        addr: IpAddr,
        port: u16,
        buffer_size: usize,
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

        let handle = {
            let mut node = MCSNode::new();
            let mut if_net_inner = if_net.inner.lock(&mut node);

            if_net_inner.socket_set.add(socket)
        };

        Ok(TcpListener {
            handle,
            interface_id,
        })
    }
    // pub fn accept(&self) -> Result<TcpStream, ()> {
    //     Ok(TcpStream {})
    // }
}
