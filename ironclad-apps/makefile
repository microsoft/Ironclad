NUBUILD=bin_tools/NuBuild/NuBuild.exe -j $(j)

all: $(NUBUILD)
	$(NUBUILD) DafnyVerifyTree src/Dafny/apps/apps.batch
#	$(NUBUILD) --html nuobj/summary.html DafnyVerifyTree src/Dafny/apps/apps.batch

$(NUBUILD):
	make -C tools/NuBuild

nuobj/test.tgz: all
	find nuobj -name \*.vdfy | tar --files-from=- -czf $@

#all:
#	tools/scripts/ironmake.py
#	+make -C obj

#test.tgz:
#	tools/scripts/ironmake.py
#	+DAFNYTIMELIMIT=120 make -C obj test.tgz

clean-dafny:
	find obj -name \*.res\* | xargs rm
