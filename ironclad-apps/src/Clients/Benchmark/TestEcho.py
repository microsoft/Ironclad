#!/usr/bin/python

import socket

from BenchSpec import *

UDP_PORT = 7
MESSAGE = "Hello, ironclad!"

sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
sock.sendto(MESSAGE, (SUT_IP, UDP_PORT))
print sock.recv(1024)
