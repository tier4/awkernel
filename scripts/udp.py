import socket
import sys
import time
import matplotlib.pyplot as plt
import numpy as np


iteration = 10000

sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
addr = ('localhost', 26099)
sock.bind(addr)

buf, raddr = sock.recvfrom(4096)

rtts = [0] * iteration

for i in range(iteration):
    t0 = time.time()
    sock.sendto(buf, raddr)

    buf, raddr = sock.recvfrom(4096)
    t1 = time.time()

    rtts[i] = t1 - t0

    if i % (iteration / 10) == 0:
        print(f'i = {i}', file=sys.stderr)


for i in range(iteration):
    rtts[i] = rtts[i] * 1000000


times = np.arange(len(rtts))
plt.figure(figsize=(12, 6))
plt.plot(times, rtts, 'b-', linewidth=1)
plt.grid(True)
plt.xlabel('Iteration')
plt.ylabel('RTT [us]')
plt.show()
