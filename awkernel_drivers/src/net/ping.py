import socket
import sys

sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
addr = ('localhost', 1111)
print('listening on %s port %s' % addr, file=sys.stderr)
sock.bind(addr)
UDP_IP = "127.0.0.1"
UDP_PORT = 4445

target = (UDP_IP, UDP_PORT)

sock.sendto(b'this is the host!', target )