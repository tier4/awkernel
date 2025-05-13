from __future__ import print_function
import socket
import time
from contextlib import closing

def main():
    local_address   = '192.168.100.1' # IPv4 address of the interface
    multicast_group = '224.0.0.124'   # Multicast group
    port = 30001

    with closing(socket.socket(socket.AF_INET, socket.SOCK_DGRAM)) as sock:

        # sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_LOOP, 0)
        sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_IF, socket.inet_aton(local_address))

        count = 0
        while True:
            message = 'Hello world : {0}'.format(count).encode('utf-8')
            print(message)
            sock.sendto(message, (multicast_group, port))
            count += 1
            time.sleep(1)

if __name__ == '__main__':
    main()
