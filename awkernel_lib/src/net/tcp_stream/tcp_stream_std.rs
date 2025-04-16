use crate::{
    net::{ip_addr::IpAddr, tcp::create_socket, NetManagerError},
    select::{EventType, FdWaker},
};

use super::{SockTcpStream, TcpResult};

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
        loop {
            match self.stream.write(buf) {
                Ok(len) => return TcpResult::Ok(len),
                Err(err) => match err.kind() {
                    ErrorKind::WouldBlock => {
                        self.fd_waker
                            .register_waker(waker.clone(), EventType::Write);
                        return TcpResult::WouldBlock;
                    }
                    ErrorKind::BrokenPipe
                    | ErrorKind::ConnectionReset
                    | ErrorKind::ConnectionAborted => return TcpResult::CloseRemote,
                    ErrorKind::Interrupted => (), // retry
                    _ => return TcpResult::InvalidState,
                },
            }
        }
    }

    fn recv(&mut self, buf: &mut [u8], waker: &core::task::Waker) -> TcpResult {
        loop {
            match self.stream.read(buf) {
                Ok(len) => {
                    if len == 0 {
                        return TcpResult::CloseRemote;
                    } else {
                        return TcpResult::Ok(len);
                    }
                }
                Err(err) => match err.kind() {
                    ErrorKind::WouldBlock => {
                        self.fd_waker.register_waker(waker.clone(), EventType::Read);
                        return TcpResult::WouldBlock;
                    }
                    ErrorKind::BrokenPipe
                    | ErrorKind::ConnectionReset
                    | ErrorKind::ConnectionAborted => return TcpResult::CloseRemote,
                    ErrorKind::Interrupted => (), // retry
                    _ => return TcpResult::InvalidState,
                },
            }
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
        let (socket, sock_addr) = create_socket(remote_addr, remote_port)?;

        // Make the socket non-blocking.
        socket
            .set_nonblocking(true)
            .or(Err(NetManagerError::SendError))?;

        // Connect.
        let raw_fd = socket.as_raw_fd();
        let mut fd_waker = FdWaker::new(raw_fd);

        loop {
            if let Err(err) = socket.connect(&sock_addr) {
                match err.kind() {
                    ErrorKind::WouldBlock | ErrorKind::InProgress => {
                        fd_waker.register_waker(waker.clone(), EventType::Write);
                        break;
                    }
                    ErrorKind::Interrupted => (), // retry
                    _ => {
                        return Err(NetManagerError::ConnectError);
                    }
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

impl TcpStream {
    pub(crate) fn new(stream: std::net::TcpStream) -> Result<Self, NetManagerError> {
        stream
            .set_nonblocking(true)
            .or(Err(NetManagerError::FailedToMakeNonblocking))?;

        let raw_fd = stream.as_raw_fd();
        let fd_waker = FdWaker::new(raw_fd);

        Ok(TcpStream { stream, fd_waker })
    }
}
