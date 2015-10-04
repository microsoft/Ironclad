#!/usr/bin/python

import tarfile
import re
import sys
import subprocess
from OutputFormatting import *

time_re = re.compile("real (\d*)m([\d.]*)s user")
disposition_parse_error_re = re.compile("Error opening file")
disposition_parse_error2_re = re.compile("(\d*) parse errors detected in")
disposition_timeouts_re = re.compile("Dafny program verifier finished with (\d*) verified, (\d*) errors*, (\d) time outs*")
disposition_notimeouts_re = re.compile("Dafny program verifier finished with (\d*) verified, (\d*) errors*")
disposition_proverdied_re = re.compile("Prover error: Prover died")

def extract_time(s):
	mo = time_re.search(s)
	if (mo==None):
		return None
	else:
		(min,sec) = mo.groups(0)
		return int(min)*60+float(sec)

class Disposition:
	def __init__(self, s):
		self.parse_failures = 0
		self.verification_errors = 0
		self.timeouts = 0
		self.succeeding_methods = 0

		mo = disposition_timeouts_re.search(s)
		if (mo!=None):
			(succeeding_methods_s,verification_errors_s,timeouts_s) = mo.groups(0)
			self.succeeding_methods = int(succeeding_methods_s)
			self.verification_errors = int(verification_errors_s)
			self.timeouts = int(timeouts_s)
			return
		mo = disposition_notimeouts_re.search(s)
		if (mo!=None):
			(succeeding_methods_s,verification_errors_s) = mo.groups(0)
			self.succeeding_methods = int(succeeding_methods_s)
			self.verification_errors = int(verification_errors_s)
			return
		mo = disposition_parse_error_re.search(s)
		if (mo!=None):
			self.parse_failures = 1
			# not really a count, just a flag.
			return
		mo = disposition_parse_error2_re.search(s)
		if (mo!=None):
			self.parse_failures = int(mo.groups(0)[0])
			return
		mo = disposition_proverdied_re.search(s)
		if (mo!=None):
			self.verification_errors = 1
			return
		print s
		raise Exception("unparsed log")
		self.parse_failures = 1
		# TODO need regex for timeouts

	def __repr__(self):
		if (self.parse_failures>0):
			return "parse_failure"
		elif (self.verification_errors>0):
			return "verification_error"
		elif (self.timeouts>0):
			return "timeout"
		else:
			return "success"

	def succeeds(self):
		return self.parse_failures==0 and self.verification_errors==0 and self.timeouts==0

COMMON_PREFIX="obj/dafny/"

class DfyRecord:
	def __init__(self, filename, time, disposition, log):
		self.filename = filename
		self.time = time
		self.disposition = disposition
		self.log = log

	def brief_name(self):
		if (self.filename.startswith(COMMON_PREFIX)):
			fn = self.filename[len(COMMON_PREFIX):]
			fn = fn.replace(".res", ".dfy")
			return fn
		else:
			return self.filename

class Summarize:
	def __init__(self, fmt, tar_fn):
		self.records = []
		self.fmt = fmt
		self.parse(tar_fn)
		self.report()

	def parse(self, tar_fn):
		self.tf = tarfile.open(tar_fn, "r:gz")

		self.total_time_sec = 0
		res_tis = filter(
			lambda ti: ti.name.endswith(".res"), self.tf.getmembers())
		for ti in res_tis:
			self.process(ti)
	
	def process(self, ti):
		res = self.tf.extractfile(ti).read()
		elapsed_time = extract_time(res)

		logname = ti.name+".log"
		log = self.tf.extractfile(logname).read()
		disposition = Disposition(log)

		record = DfyRecord(ti.name, elapsed_time, disposition, log)
		self.records.append(record)
		self.total_time_sec += record.time

	def collect_git_info_short(self):
		return subprocess.check_output(["git", "show", "-s"])

	def collect_git_info_long(self):
		return subprocess.check_output(["git", "show"])

	def report(self):
		fmt = self.fmt
		fp = sys.stdout

		failure_records = filter(lambda r: not r.disposition.succeeds(), self.records)
		failure_count = len(failure_records)
		parse_failure_count = len(filter(lambda r: r.disposition.parse_failures > 0, self.records))
		verification_error_count = len(filter(lambda r: r.disposition.verification_errors > 0, self.records))
		timeout_count = len(filter(lambda r: r.disposition.timeouts > 0, self.records))
		if (failure_count == 0):
			overall_status = "Success"
			overall_color = fmt.Green
		else:
			overall_status = "Fail"
			overall_color = fmt.Red
		git_info = self.collect_git_info_short()

		fp.write(fmt.prelude())
		fp.write(fmt.pre(git_info))
		fp.write(fmt.spacer())
		fp.write(fmt.color(overall_color, "Overall status: %s" % overall_status))
		fp.write(fmt.line("Count of files with failures: %d" % failure_count))
		fp.write(fmt.error_count_color(parse_failure_count, fmt.bullet("  Files with parse failures: %d" % parse_failure_count)))
		fp.write(fmt.error_count_color(verification_error_count, fmt.bullet("  Files with verification failures: %d" % verification_error_count)))
		fp.write(fmt.error_count_color(timeout_count, fmt.bullet("  Files with timeouts: %d" % timeout_count)))

		top_n = 10
		records_by_time = list(self.records)
		def bytime(a,b):
			return cmp(a.time, b.time)
		records_by_time.sort(bytime)
		records_by_time = records_by_time[::-1]
		fp.write(fmt.spacer())

		tt_h = int(self.total_time_sec/3600)
		tt_m = int((self.total_time_sec-tt_h*3600)/60)
		tt_s = int((self.total_time_sec-tt_h*3600-tt_m*60))
		fp.write(fmt.header("Total processing time: %.0fs (%dh%02dm%02ds)" % (
			self.total_time_sec, tt_h, tt_m, tt_s)))
		fp.write(fmt.line("Slowest %d verifications:" % top_n))
		for r in records_by_time[:top_n]:
			fp.write(fmt.error_count_color(1-r.disposition.succeeds(), "  %3.0fs %s" % (r.time, r.brief_name())))

		def byname(a,b):
			return cmp(a.filename, b.filename)
		failure_records.sort(byname)
		for r in failure_records:
			fp.write(fmt.spacer())
			fp.write(fmt.header("Failure with %s, %s:" % (r.brief_name(), r.disposition)))
			fp.write(fmt.pre(r.log))

		fp.write(fmt.spacer())
		fp.write(fmt.header("Commit details"))
		git_info = self.collect_git_info_long()
		fp.write(fmt.pre(git_info))
		fp.write(fmt.spacer())
		fp.write(fmt.epilogue())

progname = sys.argv[0]

def Usage():
	sys.stderr.write("Usage: %s [--ascii|--html] test.tgz\n" % progname)
	sys.exit(-1)

def main():
	argv = sys.argv[1:]

	fmt = FormatHTML()
	while (argv[0].startswith("--")):
		if (argv[0]=="--html"):
			fmt = FormatHTML()
			argv = argv[1:]
			continue
		if (argv[0]=="--ascii"):
			fmt = FormatASCII()
			argv = argv[1:]
			continue
		Usage()

	if (len(argv)!=1):
		Usage()

	Summarize(fmt, argv[0])

main()
