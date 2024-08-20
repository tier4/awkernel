from __future__ import print_function
import socket
from contextlib import closing

def main():
    local_address   = '192.168.100.1' # IPv4 address of the interface
    multicast_group = '224.0.0.123'   # Multicast group
    port = 20001
    bufsize = 4096

    with closing(socket.socket(socket.AF_INET, socket.SOCK_DGRAM)) as sock:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.bind(('', port))
        sock.setsockopt(socket.IPPROTO_IP,
                        socket.IP_ADD_MEMBERSHIP,
                        socket.inet_aton(multicast_group) + socket.inet_aton(local_address))

        while True:
            print(sock.recv(bufsize))

if __name__ == '__main__':
    main()
