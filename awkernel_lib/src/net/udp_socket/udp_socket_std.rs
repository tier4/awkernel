use crate::{
    net::ip_addr::IpAddr,
    select::{EventType, FdWaker},
};

use super::NetManagerError;

use std::{net::UdpSocket as StdUdpSocket, os::fd::AsRawFd};

pub struct UdpSocket {
    socket: StdUdpSocket,
    fd_waker: FdWaker,
}

impl super::SockUdp for UdpSocket {
    fn bind_on_interface(
        _interface_id: u64,
        addr: &IpAddr,
        port: Option<u16>,
        _rx_buffer_size: usize,
        _tx_buffer_size: usize,
    ) -> Result<Self, NetManagerError> {
        let port = port.unwrap_or_default();
        let addr = addr.get_addr();
        let sock_addr = std::net::SocketAddr::new(addr, port);

        let socket = StdUdpSocket::bind(sock_addr).or(Err(NetManagerError::BindError))?;

        let fd = socket.as_raw_fd();
        crate::file_control::set_nonblocking(fd)
            .or(Err(NetManagerError::FailedToMakeNonblocking))?;

        let fd_waker = FdWaker::new(fd);

        Ok(UdpSocket { socket, fd_waker })
    }

    fn send_to(
        &mut self,
        buf: &[u8],
        addr: &IpAddr,
        port: u16,
        waker: &core::task::Waker,
    ) -> Result<bool, NetManagerError> {
        let addr = addr.get_addr();
        let sock_addr = std::net::SocketAddr::new(addr, port);

        loop {
            match self.socket.send_to(buf, sock_addr) {
                Ok(_) => return Ok(true),
                Err(e) => match e.kind() {
                    std::io::ErrorKind::WouldBlock => {
                        self.fd_waker
                            .register_waker(waker.clone(), EventType::Write);
                        return Ok(false);
                    }
                    std::io::ErrorKind::Interrupted => (), // retry
                    _ => return Err(NetManagerError::SendError),
                },
            }
        }
    }

    fn recv(
        &mut self,
        buf: &mut [u8],
        waker: &core::task::Waker,
    ) -> Result<Option<(usize, IpAddr, u16)>, NetManagerError> {
        loop {
            match self.socket.recv_from(buf) {
                Ok((len, sock_addr)) => {
                    let addr = sock_addr.ip();
                    let addr = IpAddr::new(addr);
                    let port = sock_addr.port();

                    return Ok(Some((len, addr, port)));
                }
                Err(e) => match e.kind() {
                    std::io::ErrorKind::WouldBlock => {
                        self.fd_waker.register_waker(waker.clone(), EventType::Read);
                        return Ok(None);
                    }
                    std::io::ErrorKind::Interrupted => (), // retry
                    _ => return Err(NetManagerError::RecvError),
                },
            }
        }
    }

    fn join_multicast_v4(
        &mut self,
        multicast_addr: core::net::Ipv4Addr,
        interface_addr: core::net::Ipv4Addr,
    ) -> Result<(), NetManagerError> {
        log::debug!("Joining multicast group: {multicast_addr} on interface: {interface_addr}");
        self.socket
            .join_multicast_v4(&multicast_addr, &interface_addr)
            .or(Err(NetManagerError::MulticastError))
    }

    fn leave_multicast_v4(
        &mut self,
        multicast_addr: core::net::Ipv4Addr,
        interface_addr: core::net::Ipv4Addr,
    ) -> Result<(), NetManagerError> {
        self.socket
            .leave_multicast_v4(&multicast_addr, &interface_addr)
            .or(Err(NetManagerError::MulticastError))
    }
}
