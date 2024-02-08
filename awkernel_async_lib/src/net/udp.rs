use core::net::IpAddr;
use futures::Future;
use smoltcp::iface::SocketHandle;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UdpSocketError {
    SocketCreationError,
    SendError,
}

pub struct UdpSocket {
    socket_handle: SocketHandle,
    interface_id: u64,
}

impl UdpSocket {
    pub fn create_on_iface(
        interface_id: u64,
        port: u16,
        buffer_size: usize,
    ) -> Result<UdpSocket, UdpSocketError> {
        let socket_handle =
            awkernel_lib::net::create_udp_socket_ipv4_on_iface(interface_id, port, buffer_size)
                .or(Err(UdpSocketError::SocketCreationError))?;

        Ok(UdpSocket {
            socket_handle,
            interface_id,
        })
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
        match self.dst_addr {
            IpAddr::V4(addr) => {
                match awkernel_lib::net::udp_sendto_v4(
                    self.socket.interface_id,
                    self.socket.socket_handle,
                    self.data,
                    *addr,
                    self.dst_port,
                    cx.waker(),
                ) {
                    Ok(true) => core::task::Poll::Ready(Ok(())),
                    Ok(false) => core::task::Poll::Pending,
                    Err(_) => core::task::Poll::Ready(Err(UdpSocketError::SendError)),
                }
            }
            IpAddr::V6(addr) => {
                todo!()
            }
        }
    }
}
