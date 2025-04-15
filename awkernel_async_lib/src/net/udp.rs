use core::net::Ipv4Addr;

use super::IpAddr;
use awkernel_lib::net::{udp_socket::SockUdp, NetManagerError};
use futures::Future;
use pin_project::pin_project;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UdpSocketError {
    SocketCreationError,
    SendError,
    InterfaceIsNotReady,
}

#[derive(Debug, Clone)]
pub struct UdpConfig {
    pub addr: IpAddr,
    pub port: Option<u16>,
    pub rx_buffer_size: usize,
    pub tx_buffer_size: usize,
}

impl Default for UdpConfig {
    fn default() -> Self {
        UdpConfig {
            addr: IpAddr::new_v4(Ipv4Addr::new(0, 0, 0, 0)),
            port: None,
            rx_buffer_size: 1024 * 64,
            tx_buffer_size: 1024 * 64,
        }
    }
}

pub struct UdpSocket {
    socket_handle: awkernel_lib::net::udp_socket::UdpSocket,
}

impl UdpSocket {
    pub fn bind_on_interface(
        interface_id: u64,
        config: &UdpConfig,
    ) -> Result<UdpSocket, UdpSocketError> {
        let socket_handle = awkernel_lib::net::udp_socket::UdpSocket::bind_on_interface(
            interface_id,
            &config.addr,
            config.port,
            config.rx_buffer_size,
            config.tx_buffer_size,
        )
        .or(Err(UdpSocketError::SocketCreationError))?;

        Ok(UdpSocket { socket_handle })
    }

    /// Send a UDP packet to the specified address and port.
    #[inline(always)]
    pub async fn send(
        &mut self,
        data: &[u8],
        dst_addr: &IpAddr,
        dst_port: u16,
    ) -> Result<(), UdpSocketError> {
        UdpSender {
            socket: self,
            data,
            dst_addr,
            dst_port,
        }
        .await
    }

    /// Receive a UDP packet from the socket.
    /// This function returns the number of bytes read, the source address, and the source port.
    ///
    /// If the length of the received data is greater than the length of the buffer,
    /// the data is truncated to the length of the buffer.
    #[inline(always)]
    pub async fn recv(&mut self, buf: &mut [u8]) -> Result<(usize, IpAddr, u16), UdpSocketError> {
        UdpReceiver { socket: self, buf }.await
    }
}

#[pin_project]
pub struct UdpSender<'a> {
    socket: &'a mut UdpSocket,
    data: &'a [u8],
    dst_addr: &'a IpAddr,
    dst_port: u16,
}

impl Future for UdpSender<'_> {
    type Output = Result<(), UdpSocketError>;
    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let this = self.project();

        match this.socket.socket_handle.send_to(
            this.data,
            this.dst_addr,
            *this.dst_port,
            cx.waker(),
        ) {
            Ok(true) => core::task::Poll::Ready(Ok(())),
            Ok(false) => core::task::Poll::Pending,
            Err(NetManagerError::InterfaceIsNotReady) => {
                core::task::Poll::Ready(Err(UdpSocketError::InterfaceIsNotReady))
            }
            Err(_) => core::task::Poll::Ready(Err(UdpSocketError::SendError)),
        }
    }
}

#[pin_project]
pub struct UdpReceiver<'a> {
    socket: &'a mut UdpSocket,
    buf: &'a mut [u8],
}

impl Future for UdpReceiver<'_> {
    type Output = Result<(usize, IpAddr, u16), UdpSocketError>;
    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let this = self.project();

        let (socket, buf) = (this.socket, this.buf);

        match socket.socket_handle.recv(buf, cx.waker()) {
            Ok(Some(result)) => core::task::Poll::Ready(Ok(result)),
            Ok(None) => core::task::Poll::Pending,
            Err(_) => core::task::Poll::Ready(Err(UdpSocketError::SendError)),
        }
    }
}
