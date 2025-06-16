#!/usr/bin/env python3
#20200301
#Jan Mojzis
#Public domain.
# Downloaded from https://github.com/janmojzis/ntpserver

import logging
import socket
import time
import datetime
import os
import random
import sys
import struct
import getopt

NTPFORMAT = ">3B b 3I 4Q"
NTPDELTA = 2208988800.0

def s2n(t = 0.0):
        """
        System to NTP
        """

        t += NTPDELTA
        return (int(t) << 32) + int(abs(t - int(t)) * (1<<32))

def n2s(x = 0):
        """
        NTP to System
        """

        t = float(x >> 32) + float(x & 0xffffffff) / (1<<32)
        return t - NTPDELTA

def tfmt(t = 0.0):
        """
        Format System Timestamp
        """

        return datetime.datetime.fromtimestamp(t).strftime("%Y-%m-%d_%H:%M:%S.%f")

def usage():
        """
        Print the usage
        """

        print("ntpserver.py [-vh] [ip] [port] [chroot directory]", file = sys.stderr)
        sys.exit(100)

loglevel = logging.INFO

# parse program parameters
try:
        options, arguments = getopt.getopt(sys.argv[1:], 'hv')
except Exception as e:
        #bad option
        usage()

# process options
for opt, val in options:
        if opt == "-h":
                usage()
        if opt == "-v":
                loglevel = logging.DEBUG

try:
        localip = arguments[0]
except IndexError:
        localip = "0.0.0.0"

try:
        localport = int(arguments[1])
except IndexError:
        localport = 123

try:
        root = arguments[2]
except IndexError:
        root = '/var/lib/ntpserver'

logging.basicConfig(
        format='%(asctime)s %(levelname)-8s %(message)s',
        level = loglevel,
        datefmt='%Y-%m-%d_%H:%M:%S')

logging.info("starting ntpserver.py %s %d" % (localip, localport))

# chroot
if not os.path.exists(root):
        logging.warning('%s not exist, making the directory' % (root))
        os.mkdir(root)
os.chdir(root)
root = os.getcwd()
os.chroot(".")
logging.debug('chrooted into directory %s' % (root))

# create socket
s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
s.bind((localip, localport))
logging.debug('local socket: %s:%d' % s.getsockname())

# drop privileges
try:
        uid = 100000000 + 100000 * random.randint(0, 999) + os.getpid()
        os.setgid(uid)
        os.setuid(uid)
except OSError:
        uid = 10000 + random.randint(0, 9999)
        os.setgid(uid)
        os.setuid(uid)
logging.debug('UID/GID set to %d' % (uid))

# get the precision
try:
        hz = int(1 / time.clock_getres(time.CLOCK_REALTIME))
except AttributeError:
        hz = 1000000000
precision = 0
while hz > 1:
        precision -= 1;
        hz >>= 1

while True:
        try:
                # receive the query
                data, addr = s.recvfrom(struct.calcsize(NTPFORMAT))
                serverrecv = s2n(time.time())
                if len(data) != struct.calcsize(NTPFORMAT):
                        raise Exception("Invalid NTP packet: packet too short: %d bytes" % (len(data)))
                try:
                        data = struct.unpack(NTPFORMAT, data)
                except struct.error:
                        raise Exception("Invalid NTP packet: unable to parse packet")
                data = list(data)

                # parse the NTP query (only Version, Mode, Transmit Timestamp)
                version = data[0] >> 3 & 0x7
                if (version > 4):
                        raise Exception("Invalid NTP packet: bad version %d" % (version))
                mode = data[0] & 0x7
                if (mode != 3):
                        raise Exception("Invalid NTP packet: bad client mode %d" % (mode))
                clienttx = data[10]

                # create the NTP response
                data[0] = version << 3 | 4      # Leap, Version, Mode
                data[1] = 1                     # Stratum
                data[2] = 0                     # Poll
                data[3] = precision             # Precision
                data[4] = 0                     # Synchronizing Distance      
                data[5] = 0                     # Synchronizing Dispersion
                data[6] = 0                     # Reference Clock Identifier
                data[7] = serverrecv            # Reference Timestamp
                data[8] = clienttx              # Originate Timestamp
                data[9] = serverrecv            # Receive Timestamp
                data[10] = s2n(time.time())     # Transmit Timestamp

                # send the response
                data = struct.pack(NTPFORMAT, data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7], data[8], data[9], data[10])
                s.sendto(data, addr)

        except Exception as e:
                logging.warning("%s: failed: %s" % (addr[0], e))
        else:
                logging.info('%s: ok: client="%s", server="%s"' % (addr[0], tfmt(n2s(clienttx)), tfmt(n2s(serverrecv))))
