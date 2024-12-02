use core::net::Ipv4Addr;

use super::IpAddr;
use awkernel_lib::delay::uptime_nano;
use awkernel_lib::net::NetManagerError;
use core::sync::atomic::{AtomicBool, Ordering};
use futures::Future;
use pin_project::pin_project;

static mut COUNT: u64 = 0;
static mut SUM: u64 = 0;
static LOCK: AtomicBool = AtomicBool::new(false);

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

fn acquire_lock() {
    while LOCK
        .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        core::hint::spin_loop();
    }
}

fn release_lock() {
    LOCK.store(false, Ordering::Release);
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
        config: UdpConfig,
    ) -> Result<UdpSocket, UdpSocketError> {
        let socket_handle = awkernel_lib::net::udp_socket::UdpSocket::bind_on_interface(
            interface_id,
            config.addr,
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
        //let t1 = uptime_nano();
        let ret = match self.socket.socket_handle.send_to(
            self.data,
            self.dst_addr,
            self.dst_port,
            cx.waker(),
        ) {
            Ok(true) => core::task::Poll::Ready(Ok(())),
            Ok(false) => core::task::Poll::Pending,
            Err(NetManagerError::InterfaceIsNotReady) => {
                core::task::Poll::Ready(Err(UdpSocketError::InterfaceIsNotReady))
            }
            Err(_) => core::task::Poll::Ready(Err(UdpSocketError::SendError)),
        };
        //let t2 = uptime_nano();
        //unsafe {
        //acquire_lock();
        //SUM += (t2 - t1) as u64;
        //COUNT += 1;
        //if COUNT == 1000 {
        //log::info!("send_to avg: {:?}", SUM / COUNT);
        //SUM = 0;
        //COUNT = 0;
        //}
        //release_lock();
        //}

        ret
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

        //let t1 = uptime_nano();
        let ret = match socket.socket_handle.recv(buf, cx.waker()) {
            Ok(Some(result)) => core::task::Poll::Ready(Ok(result)),
            Ok(None) => core::task::Poll::Pending,
            Err(_) => core::task::Poll::Ready(Err(UdpSocketError::SendError)),
        };
        //let t2 = uptime_nano();
        //unsafe {
        //acquire_lock();
        //SUM += (t2 - t1) as u64;
        //COUNT += 1;
        //if COUNT == 1000 {
        //log::info!("send_to avg: {:?}", SUM / COUNT);
        //SUM = 0;
        //COUNT = 0;
        //}
        //release_lock();
        //}

        ret
    }
}
