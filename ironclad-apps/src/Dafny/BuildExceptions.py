# this file is included by ironmake.py

class Exceptions():
	def __init__(self):
		self.flags = {}
##############################################################################
## Add flags here:
		self.addFlag("Noise.i.dfy", "/z3opt:ARITH_RANDOM_SEED=2")
		for real_file in ["Noise.s.dfy", "Noise.i.dfy", "BigRat.i.dfy", "DiffPriv.i.dfy", "DiffPrivPerformQuery.i.dfy", "mul_nonlinear.i.dfy", "div_nonlinear.i.dfy"]:
			self.addFlag(real_file, "/z3opt:NL_ARITH=true")
##############################################################################

	def addFlag(self, basename, flagstr):
		# flagstr may contain spaces for multiple flags.
		self.flags[basename.lower()] = flagstr

	def __getitem__(self, basename):
		basename = basename.lower()
		if (basename in self.flags):
			print "Exception for %s : %s" % (basename, self.flags[basename])
			return self.flags[basename]
		return ""
