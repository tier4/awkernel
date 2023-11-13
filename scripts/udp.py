import socket
import sys


sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
addr = ('localhost', 26099)
print('listening on %s port %s' % addr, file=sys.stderr)
sock.bind(addr)

while True:
    buf, raddr = sock.recvfrom(4096)
    print(buf.decode("utf-8"), file=sys.stderr)
    print(raddr)
    sock.sendto(buf, raddr)
