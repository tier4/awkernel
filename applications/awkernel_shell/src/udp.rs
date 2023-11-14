use awkernel_async_lib::uptime;
use awkernel_lib::net::NetManager;
use awkernel_lib::{console, delay};
use smoltcp::iface::SocketSet;
use smoltcp::socket::udp;
use smoltcp::time::Instant;
use smoltcp::wire::{IpAddress, IpCidr, Ipv4Address};

pub(crate) fn udp_test() {
    let address = IpAddress::v4(10, 0, 2, 2);
    let port = 26099;

    // Create interface
    let (mut device, mut iface) = NetManager::get_iface().unwrap();

    // register the ip address
    iface.update_ip_addrs(|ip_addrs| {
        ip_addrs
            .push(IpCidr::new(IpAddress::v4(10, 0, 2, 15), 24))
            .unwrap();
    });

    // route gateway
    iface
        .routes_mut()
        .add_default_ipv4_route(Ipv4Address::new(10, 0, 2, 2))
        .unwrap();

    // Create sockets
    let udp_rx_buffer = udp::PacketBuffer::new(
        vec![udp::PacketMetadata::EMPTY, udp::PacketMetadata::EMPTY],
        vec![0; 65535],
    );
    let udp_tx_buffer = udp::PacketBuffer::new(
        vec![udp::PacketMetadata::EMPTY, udp::PacketMetadata::EMPTY],
        vec![0; 65535],
    );
    let udp_socket = udp::Socket::new(udp_rx_buffer, udp_tx_buffer);

    let mut sockets = SocketSet::new(vec![]);
    let udp_handle = sockets.add(udp_socket);

    let socket = sockets.get_mut::<udp::Socket>(udp_handle);
    socket.bind(2000).unwrap();

    loop {
        let timestamp = Instant::from_micros(uptime() as i64);

        iface.poll(timestamp, &mut device, &mut sockets);
        let socket = sockets.get_mut::<udp::Socket>(udp_handle);

        if socket.can_send() {
            socket
                .send_slice(b"HELLO FROM AUTOWARE KERNEL", (address, port))
                .unwrap();
        }

        if socket.recv().is_ok() {
            console::print("+");
        } else {
            console::print(".");
        }

        delay::wait_millisec(1);
    }
}
