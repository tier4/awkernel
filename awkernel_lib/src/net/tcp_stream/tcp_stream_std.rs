use socket2::{Domain, Protocol, SockAddr, Socket, Type};

use crate::{
    net::{ip_addr::IpAddr, NetManagerError},
    select::{EventType, FdWaker},
};

use super::{SockTcpStream, TcpResult};

use core::net::SocketAddr;
use std::{
    io::{ErrorKind, Read, Write},
    net::TcpStream as StdTcpStream,
    os::fd::AsRawFd,
};

pub struct TcpStream {
    stream: StdTcpStream,
    fd_waker: FdWaker,
}

impl SockTcpStream for TcpStream {
    fn send(&mut self, buf: &[u8], waker: &core::task::Waker) -> TcpResult {
        match self.stream.write(buf) {
            Ok(len) => TcpResult::Ok(len),
            Err(err) => match err.kind() {
                ErrorKind::WouldBlock => {
                    self.fd_waker
                        .register_waker(waker.clone(), EventType::Write);
                    TcpResult::WouldBlock
                }
                ErrorKind::BrokenPipe
                | ErrorKind::ConnectionReset
                | ErrorKind::ConnectionAborted => TcpResult::CloseRemote,
                _ => TcpResult::InvalidState,
            },
        }
    }

    fn recv(&mut self, buf: &mut [u8], waker: &core::task::Waker) -> TcpResult {
        match self.stream.read(buf) {
            Ok(len) => {
                if len == 0 {
                    TcpResult::CloseRemote
                } else {
                    TcpResult::Ok(len)
                }
            }
            Err(err) => match err.kind() {
                ErrorKind::WouldBlock => {
                    self.fd_waker.register_waker(waker.clone(), EventType::Read);
                    TcpResult::WouldBlock
                }
                ErrorKind::BrokenPipe
                | ErrorKind::ConnectionReset
                | ErrorKind::ConnectionAborted => TcpResult::CloseRemote,
                _ => TcpResult::InvalidState,
            },
        }
    }

    fn connect(
        _interface_id: u64,
        remote_addr: &IpAddr,
        remote_port: u16,
        _rx_buffer_size: usize,
        _tx_buffer_size: usize,
        waker: &core::task::Waker,
    ) -> Result<Self, NetManagerError> {
        // Create a socket address.
        let ip = remote_addr.get_addr();
        let socket_addr = SocketAddr::new(ip, remote_port);
        let sock_addr = SockAddr::from(socket_addr);

        // Create a socket.
        let socket = Socket::new(Domain::IPV4, Type::STREAM, Some(Protocol::TCP))
            .or(Err(NetManagerError::SocketError))?;

        // Make the socket non-blocking.
        socket
            .set_nonblocking(true)
            .or(Err(NetManagerError::SendError))?;

        // Connect.
        let raw_fd = socket.as_raw_fd();
        let mut fd_waker = FdWaker::new(raw_fd);

        if let Err(err) = socket.connect(&sock_addr) {
            match err.kind() {
                ErrorKind::WouldBlock | ErrorKind::InProgress => {
                    fd_waker.register_waker(waker.clone(), EventType::Write);
                }
                _ => {
                    return Err(NetManagerError::ConnectError);
                }
            }
        }

        Ok(TcpStream {
            stream: StdTcpStream::from(socket),
            fd_waker,
        })
    }

    fn remote_addr(&self) -> Result<(IpAddr, u16), NetManagerError> {
        self.stream
            .peer_addr()
            .map(|addr| {
                let ip = IpAddr::new(addr.ip());
                let port = addr.port();
                (ip, port)
            })
            .map_err(|_| NetManagerError::SocketError)
    }
}
