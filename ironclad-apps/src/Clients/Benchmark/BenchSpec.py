
SUT_IP="157.54.148.142"


# Converted (manually) from BenchmarkList.i.dfy
BenchmarkList = {
"Nothing" : 0,
"Sha1" : 1,
"Sha256" : 2,
"RsaKeyGen" : 3,
"RsaEncrypt" : 4,
"RsaDecrypt" : 5,
"RsaDigestedSign" : 6,
"RsaDigestedVerify" : 7,
"TpmExtractRandom" : 8,
"ByteSeqToWordSeq" : 9,
"WordSeqToByteSeq" : 10,
#"Sha1Raw" : 11,
#"Sha256Raw" : 12,
"DuplicateArray" : 13,
"Max" : 14,
}

class BenchSpec():
	def __init__(self, benchmark, iterations, key_length, message_length, use_words=False, use_original=False, annotation="", elapsed_time=None):
		self.benchmark = benchmark
		self.iterations = iterations
		self.key_length = key_length
		self.message_length = message_length
		self.use_words = use_words
		self.use_original = use_original
		self.annotation = annotation
		self.elapsed_time = elapsed_time

	def tuple(self):
		return (self.benchmark, self.iterations, self.key_length, self.message_length, self.use_words, self.use_original, self.annotation, self.elapsed_time)

	def __repr__(self):
		return "BenchSpec"+str(self.tuple())+","

	def spec_tuple(self):
		return (self.benchmark, self.iterations, self.key_length, self.message_length, self.use_words, self.use_original, self.annotation)

	def compatible(self, other):
		return self.spec_tuple() == other.spec_tuple()

