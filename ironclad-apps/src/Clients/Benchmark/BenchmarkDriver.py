#!/usr/bin/python

import subprocess
import re
from BenchSpec import *

class HelpfulRE:
	def __init__(self, pattern):
		self.pattern = pattern
		self.reob = re.compile(pattern, re.MULTILINE)

class BenchmarkDriver:
	def __init__(self):
		self.re_elapsed_time = HelpfulRE("^Elapsed Time.*: (.*)$")

		self.suite3()

	def regrab(self, text, re):
		mo = re.reob.search(text)
		if (mo==None):
			print text
			raise Exception("Failed to find %s" % re.pattern)
		return mo.groups(0)[0]

	def execute_test(self, spec):
		test_id = BenchmarkList[spec.benchmark]
		cmd = ["./BenchmarkRequestCmd/bin/Debug/BenchmarkRequestCmd.exe", SUT_IP, str(test_id), str(spec.iterations), str(spec.key_length), str(spec.message_length), str(1 if spec.use_words else 0), str(1 if spec.use_original else 0)]
		print "sending: %s" % (" ".join(cmd))
		stdout_text = subprocess.check_output(cmd)
		result = self.parse_reply(stdout_text, spec.annotation)
		spec.elapsed_time = result
		print "spec  :",spec

	def parse_reply(self, text, annotation):
		text = text.replace("\r", "")
		return float(self.regrab(text, self.re_elapsed_time))

	def suite0(self):
		#for bench in ["Sha1", "Sha256","ByteSeqToWordSeq", "WordSeqToByteSeq"]:
		for bench in ["Sha256" ]:
			for block_size in [32768]:
				iterations=32768
				self.execute_test(BenchSpec(bench, iterations, 0, block_size))
		for reps in range(20):
			self.execute_test(BenchSpec("TpmExtractRandom", 1024, 1024))

	def suite1(self):
		for loops in range(10):
			for block_size in (512,):
				self.execute_test(BenchSpec("RsaKeyGen", 4, block_size))

	def suite2(self):
		for reps in range(20):
			self.execute_test(BenchSpec("TpmExtractRandom", 16, 1024))

	def suite3(self):
		#for block_size in (32,64,128,256,512,1024,2048):
			#self.execute_test(BenchSpec("RsaKeyGen", 1, block_size))
		# valid combinations: 512/32, 1024/64
		# block_size := greatest power of two less than or equal to key_size_bits/8-12.
		key_size_bits = 1024
		block_size_bytes = 64

		# create a key to encrypt against.
		self.execute_test(BenchSpec("RsaKeyGen", 1, key_size_bits, 0))
		for i in range(10):
			self.execute_test(BenchSpec("RsaDecrypt", 8, key_size_bits, block_size_bytes, annotation="key_size_bits=%s"%key_size_bits))
			self.execute_test(BenchSpec("RsaEncrypt", 8, key_size_bits, block_size_bytes, annotation="key_size_bits=%s"%key_size_bits))

BenchmarkDriver()
