import socket
import sys
import time
from datetime import datetime

# create output file name with timestamp
timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
output_file = f"rtt_log_{timestamp}.txt"

sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
addr = ('localhost', 26099)
sock.bind(addr)

buf, raddr = sock.recvfrom(4096)

while True:
    t0 = time.time()
    sock.sendto(buf, raddr)

    buf, raddr = sock.recvfrom(4096)
    t1 = time.time()

    rtt = (t1 - t0) * 1000000
    print(f'RTT: {rtt} [us]', file=sys.stderr)

    # save rtt to file
    with open(output_file, 'a') as f:
        f.write(f'{rtt}\n')

    time.sleep(0.1)