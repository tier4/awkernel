use alloc::vec::Vec;
use awkernel_lib::net::socket::IpAddr;
use futures::Future;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UdpSocketError {
    SocketCreationError,
    SendError,
}

pub struct UdpSocket {
    socket_handle: awkernel_lib::net::socket::UdpSocket,
}

impl UdpSocket {
    pub fn create_on_interface(
        interface_id: u64,
        port: u16,
        buffer_size: usize,
    ) -> Result<UdpSocket, UdpSocketError> {
        let socket_handle = awkernel_lib::net::socket::UdpSocket::create_ipv4_on_iface(
            interface_id,
            port,
            buffer_size,
        )
        .or(Err(UdpSocketError::SocketCreationError))?;

        Ok(UdpSocket { socket_handle })
    }

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

    pub async fn recv(&mut self) -> Result<(Vec<u8>, IpAddr, u16), UdpSocketError> {
        UdpReceiver { socket: self }.await
    }
}

pub struct UdpSender<'a> {
    socket: &'a mut UdpSocket,
    data: &'a [u8],
    dst_addr: &'a IpAddr,
    dst_port: u16,
}

impl<'a> Future for UdpSender<'a> {
    type Output = Result<(), UdpSocketError>;
    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        match self
            .socket
            .socket_handle
            .sendto(self.data, self.dst_addr, self.dst_port, cx.waker())
        {
            Ok(true) => core::task::Poll::Ready(Ok(())),
            Ok(false) => core::task::Poll::Pending,
            Err(_) => core::task::Poll::Ready(Err(UdpSocketError::SendError)),
        }
    }
}
pub struct UdpReceiver<'a> {
    socket: &'a mut UdpSocket,
}

impl<'a> Future for UdpReceiver<'a> {
    type Output = Result<(Vec<u8>, IpAddr, u16), UdpSocketError>;
    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        match self.socket.socket_handle.recv(cx.waker()) {
            Ok(Some(result)) => core::task::Poll::Ready(Ok(result)),
            Ok(None) => core::task::Poll::Pending,
            Err(_) => core::task::Poll::Ready(Err(UdpSocketError::SendError)),
        }
    }
}
