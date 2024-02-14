use super::IpAddr;
use awkernel_lib::net::NetManagerError;
use futures::Future;
use pin_project::pin_project;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TcpSocketError {
    SocketCreationError,
}

pub struct TcpListener {
    listener: awkernel_lib::net::tcp_listener::TcpListener,
}

impl TcpListener {
    pub fn bind_on_interface(
        interface_id: u64,
        addr: IpAddr,
        port: u16,
        buffer_size: usize,
        num_waiting_connections: usize,
    ) -> Result<TcpListener, NetManagerError> {
        let listener = awkernel_lib::net::tcp_listener::TcpListener::bind_on_interface(
            interface_id,
            addr,
            port,
            buffer_size,
            num_waiting_connections,
        )?;

        Ok(TcpListener { listener })
    }

    pub async fn accept(&mut self) -> Result<TcpStream, TcpSocketError> {
        TcpAccepter { listener: self }.await
    }
}

#[pin_project]
struct TcpAccepter<'a> {
    listener: &'a mut TcpListener,
}

impl Future for TcpAccepter<'_> {
    type Output = Result<TcpStream, TcpSocketError>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context,
    ) -> core::task::Poll<Self::Output> {
        let this = self.project();
        let listener = this.listener;
        let result = listener.listener.accept(cx.waker());
        match result {
            Ok(None) => core::task::Poll::Pending,
            Ok(Some(stream)) => core::task::Poll::Ready(Ok(TcpStream { stream })),
            Err(_e) => core::task::Poll::Ready(Err(TcpSocketError::SocketCreationError)),
        }
    }
}

pub struct TcpStream {
    stream: awkernel_lib::net::tcp_stream::TcpStream,
}
