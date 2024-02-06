use smoltcp::socket::udp::Socket;

pub struct UdpSocket {
    socket: Socket<'static>,
}

impl UdpSocket {
    pub fn bind(_addr: &str) -> Result<UdpSocket, ()> {
        todo!()
    }
}
