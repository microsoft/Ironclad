#!/usr/bin/python

import re
from numpy import *
from BenchSpec import BenchSpec

data = [
#BenchSpec('RsaKeyGen', 1, 1024, '', 194.5417),
#BenchSpec('RsaKeyGen', 1, 1024, '', 277.6209),
#BenchSpec('RsaKeyGen', 1, 1024, '', 479.9764),
#BenchSpec('RsaKeyGen', 1, 1024, '', 410.7493),
#BenchSpec('RsaKeyGen', 1, 1024, '', 995.0421),
#BenchSpec('RsaKeyGen', 1, 1024, '', 185.5208),
#BenchSpec('RsaKeyGen', 1, 1024, '', 271.9875),
#BenchSpec('RsaKeyGen', 1, 1024, '', 214.8805),
#BenchSpec('RsaKeyGen', 1, 1024, '', 243.2842),
#BenchSpec('RsaKeyGen', 1, 1024, '', 471.1768),
#
## Before Canonicalizing
#BenchSpec('RsaKeyGen', 1, 512, '', 16.77731),
#BenchSpec('RsaKeyGen', 1, 512, '', 29.44297),
#BenchSpec('RsaKeyGen', 1, 512, '', 25.03836),
#BenchSpec('RsaKeyGen', 1, 512, '', 13.80892),
#BenchSpec('RsaKeyGen', 1, 512, '', 7.543423),
#BenchSpec('RsaKeyGen', 1, 512, '', 20.06039),
#BenchSpec('RsaKeyGen', 1, 512, '', 73.0106),
#BenchSpec('RsaKeyGen', 1, 512, '', 17.2482),
#BenchSpec('RsaKeyGen', 1, 512, '', 23.70473),
#BenchSpec('RsaKeyGen', 1, 512, '', 26.22202),
#
## After Canonicalizing
#BenchSpec('RsaKeyGen', 1, 512, '', 25.52086),
#BenchSpec('RsaKeyGen', 1, 512, '', 40.67058),
#BenchSpec('RsaKeyGen', 1, 512, '', 12.83777),
#BenchSpec('RsaKeyGen', 1, 512, '', 11.71982),
#BenchSpec('RsaKeyGen', 1, 512, '', 31.66075),
#BenchSpec('RsaKeyGen', 1, 512, '', 17.82285),
#BenchSpec('RsaKeyGen', 1, 512, '', 9.800225),
#BenchSpec('RsaKeyGen', 1, 512, '', 8.215545),
#BenchSpec('RsaKeyGen', 1, 512, '', 11.95486),
#BenchSpec('RsaKeyGen', 1, 512, '', 6.170479),
#
#BenchSpec('RsaDecrypt', 8, 32, '', 3.906329),
#BenchSpec('RsaDecrypt', 8, 32, '', 3.906904),
#BenchSpec('RsaDecrypt', 8, 32, '', 3.907146),
#BenchSpec('RsaDecrypt', 8, 32, '', 3.907072),
#BenchSpec('RsaDecrypt', 8, 32, '', 3.906528),
#BenchSpec('RsaDecrypt', 8, 32, '', 3.906117),
#BenchSpec('RsaDecrypt', 8, 32, '', 3.904497),
#BenchSpec('RsaDecrypt', 8, 32, '', 3.904088),
#BenchSpec('RsaDecrypt', 8, 32, '', 3.907179),
#BenchSpec('RsaDecrypt', 8, 32, '', 3.906088),
#
#BenchSpec('RsaEncrypt', 8, 32, '', 0.9219429),
#BenchSpec('RsaEncrypt', 8, 32, '', 0.9286233),
#BenchSpec('RsaEncrypt', 8, 32, '', 0.9285086),
#BenchSpec('RsaEncrypt', 8, 32, '', 0.9285977),
#BenchSpec('RsaEncrypt', 8, 32, '', 0.9280463),
#BenchSpec('RsaEncrypt', 8, 32, '', 0.927805),
#BenchSpec('RsaEncrypt', 8, 32, '', 0.9287491),
#BenchSpec('RsaEncrypt', 8, 32, '', 0.9285343),
#BenchSpec('RsaEncrypt', 8, 32, '', 0.9285265),
#BenchSpec('RsaEncrypt', 8, 32, '', 0.9286342),
#
#BenchSpec('RsaKeyGen', 1, 1024, '', 327.0056),
#BenchSpec('RsaDecrypt', 8, 64, '', 49.4005),
#BenchSpec('RsaEncrypt', 8, 64, '', 2.30449),
#BenchSpec('RsaDecrypt', 8, 64, '', 49.41412),
#BenchSpec('RsaEncrypt', 8, 64, '', 2.304769),
#BenchSpec('RsaDecrypt', 8, 64, '', 49.40992),
#BenchSpec('RsaEncrypt', 8, 64, '', 2.304908),
#BenchSpec('RsaDecrypt', 8, 64, '', 49.4192),
#BenchSpec('RsaEncrypt', 8, 64, '', 2.305215),
#BenchSpec('RsaDecrypt', 8, 64, '', 49.41233),
#BenchSpec('RsaEncrypt', 8, 64, '', 2.304783),
#BenchSpec('RsaDecrypt', 8, 64, '', 49.41201),
#BenchSpec('RsaEncrypt', 8, 64, '', 2.304904),
#BenchSpec('RsaDecrypt', 8, 64, '', 49.40812),
#BenchSpec('RsaEncrypt', 8, 64, '', 2.306457),
#BenchSpec('RsaDecrypt', 8, 64, '', 49.4155),
#BenchSpec('RsaEncrypt', 8, 64, '', 2.305282),
#BenchSpec('RsaDecrypt', 8, 64, '', 49.41673),
#BenchSpec('RsaEncrypt', 8, 64, '', 2.304551),
#BenchSpec('RsaDecrypt', 8, 64, '', 49.41605),
#BenchSpec('RsaEncrypt', 8, 64, '', 2.304723),
#
## After Add32_unrolled_8 optimization, setting MR to 8.
#BenchSpec('RsaKeyGen-u', 4, 512, '', 80.74383),
#BenchSpec('RsaKeyGen-u', 4, 512, '', 73.37518),
#BenchSpec('RsaKeyGen-u', 4, 512, '', 58.45101),
#BenchSpec('RsaKeyGen-u', 4, 512, '', 60.88408),
#BenchSpec('RsaKeyGen-u', 4, 512, '', 64.99814),
#BenchSpec('RsaKeyGen-u', 4, 512, '', 48.6908),
#BenchSpec('RsaKeyGen-u', 4, 512, '', 35.17658),
#BenchSpec('RsaKeyGen-u', 4, 512, '', 70.93044),
#BenchSpec('RsaKeyGen-u', 4, 512, '', 88.05916),
#BenchSpec('RsaKeyGen-u', 4, 1024, '', 592.9341),
#BenchSpec('RsaKeyGen-u', 4, 1024, '', 1156.92),
#
#BenchSpec('RsaKeyGen-v', 4, 512, '', 203.6944),
#BenchSpec('RsaKeyGen-v', 4, 512, '', 142.6029),
#BenchSpec('RsaKeyGen-v', 4, 512, '', 328.2928),
#BenchSpec('RsaKeyGen-v', 4, 512, '', 186.0192),
#BenchSpec('RsaKeyGen-v', 4, 512, '', 178.2307),
#BenchSpec('RsaKeyGen-v', 4, 512, '', 188.0875),
#BenchSpec('RsaKeyGen-v', 4, 512, '', 181.3387),
#BenchSpec('RsaKeyGen-v', 4, 512, '', 144.2986),
#BenchSpec('RsaKeyGen-v', 4, 512, '', 306.3781),
#BenchSpec('RsaKeyGen-v', 4, 512, '', 94.22977),
#BenchSpec('RsaKeyGen-v', 4, 512, '', 208.8214),
#
#BenchSpec('RsaDecrypt-v', 8, 32, '', 8.302419),
#BenchSpec('RsaEncrypt-v', 8, 32, '', 0.9127128),
#BenchSpec('RsaDecrypt-v', 8, 32, '', 8.301742),
#BenchSpec('RsaEncrypt-v', 8, 32, '', 0.9122038),
#BenchSpec('RsaDecrypt-v', 8, 32, '', 8.302255),
#BenchSpec('RsaEncrypt-v', 8, 32, '', 0.9126821),
#BenchSpec('RsaDecrypt-v', 8, 32, '', 8.301459),
#BenchSpec('RsaEncrypt-v', 8, 32, '', 0.9123324),
#BenchSpec('RsaDecrypt-v', 8, 32, '', 8.301554),
#BenchSpec('RsaEncrypt-v', 8, 32, '', 0.9124045),
#BenchSpec('RsaDecrypt-v', 8, 32, '', 8.301258),
#BenchSpec('RsaEncrypt-v', 8, 32, '', 0.9122229),
#BenchSpec('RsaDecrypt-v', 8, 32, '', 8.302022),
#BenchSpec('RsaEncrypt-v', 8, 32, '', 0.9121833),
#BenchSpec('RsaDecrypt-v', 8, 32, '', 8.301646),
#BenchSpec('RsaEncrypt-v', 8, 32, '', 0.912534),
#BenchSpec('RsaDecrypt-v', 8, 32, '', 8.302246),
#BenchSpec('RsaEncrypt-v', 8, 32, '', 0.9125597),
#BenchSpec('RsaDecrypt-v', 8, 32, '', 8.301321),
#BenchSpec('RsaEncrypt-v', 8, 32, '', 0.9054516),
#
#BenchSpec('RsaKeyGen-v', 1, 512, '', 36.56007),
#BenchSpec('RsaDecrypt-v', 8, 32, 'key_size_bits=512', 8.084312),
#BenchSpec('RsaEncrypt-v', 8, 32, 'key_size_bits=512', 0.9064715),
#BenchSpec('RsaDecrypt-v', 8, 32, 'key_size_bits=512', 8.084259),
#BenchSpec('RsaEncrypt-v', 8, 32, 'key_size_bits=512', 0.9062216),
#BenchSpec('RsaDecrypt-v', 8, 32, 'key_size_bits=512', 8.084807),
#BenchSpec('RsaEncrypt-v', 8, 32, 'key_size_bits=512', 0.9061556),
#BenchSpec('RsaDecrypt-v', 8, 32, 'key_size_bits=512', 8.084284),
#BenchSpec('RsaEncrypt-v', 8, 32, 'key_size_bits=512', 0.906733),
#BenchSpec('RsaDecrypt-v', 8, 32, 'key_size_bits=512', 8.084139),
#BenchSpec('RsaEncrypt-v', 8, 32, 'key_size_bits=512', 0.9060693),
#BenchSpec('RsaDecrypt-v', 8, 32, 'key_size_bits=512', 8.084414),
#BenchSpec('RsaEncrypt-v', 8, 32, 'key_size_bits=512', 0.9062116),
#BenchSpec('RsaDecrypt-v', 8, 32, 'key_size_bits=512', 8.084597),
#BenchSpec('RsaEncrypt-v', 8, 32, 'key_size_bits=512', 0.9064325),
#BenchSpec('RsaDecrypt-v', 8, 32, 'key_size_bits=512', 8.084273),
#BenchSpec('RsaEncrypt-v', 8, 32, 'key_size_bits=512', 0.8996112),
#BenchSpec('RsaDecrypt-v', 8, 32, 'key_size_bits=512', 8.084738),
#BenchSpec('RsaEncrypt-v', 8, 32, 'key_size_bits=512', 0.9063217),
#BenchSpec('RsaDecrypt-v', 8, 32, 'key_size_bits=512', 8.0843),
#BenchSpec('RsaEncrypt-v', 8, 32, 'key_size_bits=512', 0.9063667),

# After enabling reciprocal estimator and fleetnatmul together (b3b8b0595701d467d8d7d432d673a8af9c3afb5f)
#BenchSpec('RsaKeyGen', 1, 1024, 0, False, False, '', 12.13395),
#BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.7093437),
#BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2144841),
#BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.7089711),
#BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2206407),
#BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.7149615),
#BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2142338),
#BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.7045),
#BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2206872)

# After enabling optimized assembly code for mul inner loop (725911c92ba3c3b54d9332c24fc50a26c8b2bdfe)
BenchSpec('RsaKeyGen', 1, 1024, 0, False, False, '', 27.34745),
BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.1813447),
BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2059516),
BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.18114),
BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2123457),
BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.1819137),
BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2059879),
BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.1821488),
BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2059782),
BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.1858502),
BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.212652),
BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.1829405),
BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2059838),
BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.1820654),
BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2126007),
BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.1808525),
BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2060691),
BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.1799968),
BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2058071),
BenchSpec('RsaDecrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.1813919),
BenchSpec('RsaEncrypt', 8, 1024, 64, False, False, 'key_size_bits=1024', 0.2059153),

]

def parse_openssl(label, text):
	data = []
#	mo = re.compile("-DOPENSSL_(IA32_\S*)", re.MULTILINE).search(text)
#	config = mo.groups(0)[0]
	reob = re.compile("Doing (.*) for .*s on (.*) size blocks: (\S*) .*in (.*)s")
	for line in text.split("\n"):
		line = line.strip()
		mo = reob.search(line)
		if (mo!=None):
			benchmark,block_size,iterations,elapsed_time = mo.groups(0)
			data += [BenchSpec(
				"%s-%s" % (benchmark.capitalize(), label),
				int(iterations),
				int(block_size),
				float(elapsed_time))]
	return data

data += parse_openssl("openssl-101g-noasm", """
		jonh@bilbao:~/openssl-1.0.1g$ ./apps/openssl speed sha1 sha256
WARNING: can't open config file: /usr/local/ssl/openssl.cnf
Doing sha1 for 3s on 16 size blocks: 2710384 sha1's in 3.00s
Doing sha1 for 3s on 64 size blocks: 2021935 sha1's in 3.00s
Doing sha1 for 3s on 256 size blocks: 1142245 sha1's in 3.00s
Doing sha1 for 3s on 1024 size blocks: 417454 sha1's in 3.00s
Doing sha1 for 3s on 8192 size blocks: 60375 sha1's in 3.00s
Doing sha256 for 3s on 16 size blocks: 3497661 sha256's in 3.00s
Doing sha256 for 3s on 64 size blocks: 2048970 sha256's in 3.00s
Doing sha256 for 3s on 256 size blocks: 908001 sha256's in 3.00s
Doing sha256 for 3s on 1024 size blocks: 282259 sha256's in 2.99s
Doing sha256 for 3s on 8192 size blocks: 37976 sha256's in 3.00s
OpenSSL 1.0.1g 7 Apr 2014
built on: Fri Apr 25 17:21:07 PDT 2014
options:bn(64,32) rc4(idx,int) des(ptr,risc1,16,long) aes(partial) idea(int) blowfish(idx)
compiler: gcc -DOPENSSL_THREADS -D_REENTRANT -DDSO_DLFCN -DHAVE_DLFCN_H -DL_ENDIAN -DTERMIO -O3 -fomit-frame-pointer -Wall
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes   1024 bytes   8192 bytes
sha1             14455.38k    43134.61k    97471.57k   142490.97k   164864.00k
sha256           18654.19k    43711.36k    77482.75k    96666.63k   103699.80k
""")

data += parse_openssl("openssl-101g-sse2", """
jonh@bilbao:~/openssl-1.0.1g-sse2$ ./apps/openssl speed sha1 sha256
WARNING: can't open config file: /usr/local/ssl/openssl.cnf
Doing sha1 for 3s on 16 size blocks: 4441307 sha1's in 3.00s
Doing sha1 for 3s on 64 size blocks: 3619553 sha1's in 3.00s
Doing sha1 for 3s on 256 size blocks: 2350814 sha1's in 3.00s
Doing sha1 for 3s on 1024 size blocks: 977702 sha1's in 3.00s
Doing sha1 for 3s on 8192 size blocks: 152203 sha1's in 3.00s
Doing sha256 for 3s on 16 size blocks: 5747552 sha256's in 2.99s
Doing sha256 for 3s on 64 size blocks: 3207098 sha256's in 3.00s
Doing sha256 for 3s on 256 size blocks: 1355615 sha256's in 3.00s
Doing sha256 for 3s on 1024 size blocks: 413892 sha256's in 3.00s
Doing sha256 for 3s on 8192 size blocks: 55292 sha256's in 3.00s
OpenSSL 1.0.1g 7 Apr 2014
built on: Fri Apr 25 17:32:19 PDT 2014
options:bn(64,32) rc4(8x,mmx) des(ptr,risc1,16,long) aes(partial) idea(int) blowfish(idx)
compiler: gcc -DOPENSSL_THREADS -D_REENTRANT -DDSO_DLFCN -DHAVE_DLFCN_H -Wa,--noexecstack -DL_ENDIAN -DTERMIO -O3 -fomit-frame-pointer -Wall -DOPENSSL_BN_ASM_PART_WORDS -DOPENSSL_IA32_SSE2 -DOPENSSL_BN_ASM_MONT -DOPENSSL_BN_ASM_GF2m -DSHA1_ASM -DSHA256_ASM -DSHA512_ASM -DMD5_ASM -DRMD160_ASM -DAES_ASM -DVPAES_ASM -DWHIRLPOOL_ASM -DGHASH_ASM
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes   1024 bytes   8192 bytes
sha1             23686.97k    77217.13k   200602.79k   333722.28k   415615.66k
sha256           30756.13k    68418.09k   115679.15k   141275.14k   150984.02k
""")

data += parse_openssl("polarssl-1.3.6-O2", """
jonh@bilbao:~/polarssl-speedtest$ ./polarssl-speedtest
Doing sha1 for awhiles on 16 size blocks: 6000000 sha1's in 2.847s
Doing sha1 for awhiles on 64 size blocks: 3500000 sha1's in 2.944s
Doing sha1 for awhiles on 256 size blocks: 2000000 sha1's in 3.944s
Doing sha1 for awhiles on 1024 size blocks: 500000 sha1's in 3.238s
Doing sha1 for awhiles on 8192 size blocks: 70000 sha1's in 3.409s
Doing sha256 for awhiles on 16 size blocks: 6000000 sha256's in 3.188s
Doing sha256 for awhiles on 64 size blocks: 3500000 sha256's in 3.329s
Doing sha256 for awhiles on 256 size blocks: 1500000 sha256's in 3.333s
Doing sha256 for awhiles on 1024 size blocks: 400000 sha256's in 2.933s
Doing sha256 for awhiles on 8192 size blocks: 50000 sha256's in 2.748s
""")

benchmarks = list(set(map(lambda b: b.benchmark, data)))
benchmarks.sort()

def Mean(benchmark, points):
	A = array(points)
	X = A[:,0]
	Y = A[:,1]
	print "%s @ x=%s" % (benchmark, X[0])
	print "  mean %f std %f (%.0f%%)" % (
		mean(Y), std(Y), 100.0*std(Y)/mean(Y))

def Means(benchmark, points):
	A = array(points)
	X = A[:,0]
	Y = A[:,1]
	xs = list(set(X))
	xs.sort()
	for x in xs:
		subpoints = filter(lambda p: p[0]==x, points)
		Mean(benchmark, subpoints)

def LinearRegression(benchmark, points):
	A = array(points)
	X = A[:,0]
	Y = A[:,1]
	X1 = array([ X, ones(len(X)) ])
	w = linalg.lstsq(X1.T,Y)[0]
	print benchmark
	print "  %f ns s/B b=%f ns" % (w[0]*1e9, w[1]*1e9)
	#print w

for benchmark in benchmarks:
	print "==>",benchmark
	points = map(lambda b: (b.message_length, b.elapsed_time/b.iterations),
			filter(lambda b: b.benchmark==benchmark, data))
	if (benchmark.startswith("Sha")):
		LinearRegression(benchmark, points)
	else:
		Means(benchmark, points)

