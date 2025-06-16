use std::os::fd::AsRawFd;

use crate::{
    net::{ip_addr::IpAddr, tcp::create_socket, tcp_stream::TcpStream, NetManagerError},
    select::FdWaker,
};

use super::SockTcpListener;

pub struct TcpListener {
    sock: std::net::TcpListener,
    fd_waker: FdWaker,
}

impl SockTcpListener<TcpStream> for TcpListener {
    fn bind_on_interface(
        _interface_id: u64,
        addr: &IpAddr,
        port: Option<u16>,
        _rx_buffer_size: usize,
        _tx_buffer_size: usize,
        backlogs: usize,
    ) -> Result<Self, NetManagerError> {
        let (socket, sock_addr) = create_socket(addr, port.unwrap_or(0))?;

        socket
            .bind(&sock_addr)
            .or(Err(NetManagerError::BindError))?;

        socket
            .listen(backlogs as _)
            .or(Err(NetManagerError::ListenError))?;

        let sock: std::net::TcpListener = socket.into();

        sock.set_nonblocking(true)
            .or(Err(NetManagerError::FailedToMakeNonblocking))?;

        let raw_fd = sock.as_raw_fd();
        let fd_waker = FdWaker::new(raw_fd);

        Ok(TcpListener { sock, fd_waker })
    }

    fn accept(&mut self, waker: &core::task::Waker) -> Result<Option<TcpStream>, NetManagerError> {
        loop {
            match self.sock.accept() {
                Ok((stream, _)) => {
                    return Ok(Some(crate::net::tcp_stream::TcpStream::new(stream)?));
                }
                Err(e) => match e.kind() {
                    std::io::ErrorKind::WouldBlock => {
                        self.fd_waker
                            .register_waker(waker.clone(), crate::select::EventType::Read);
                        return Ok(None);
                    }
                    std::io::ErrorKind::Interrupted | std::io::ErrorKind::ConnectionAborted => (), // retry
                    _ => return Err(NetManagerError::AcceptError),
                },
            }
        }
    }
}
