//--
// <copyright file="EntryStitcherVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    internal class EntryStitcherVerb
        : Verb
    {
        private const int version = 10;
        private const string SENTINEL_APP_SPECIFIC_GOES_HERE = "//- SENTINEL_APP_SPECIFIC_GOES_HERE";

        private string appLabel;
        private IContextGeneratingVerb context;    // Label our abstractIdentifier
        private BeatVerb mainBeatVerb;
        private SourcePath genericStitch;
        private SourcePath appSpecificStitch;

        private BuildObject dafnyMainImpInput;
        private BuildObject dafnyMainIfcInput;
        private SourcePath entryImpInput;

        public EntryStitcherVerb(IContextGeneratingVerb context, string appLabel)
        {
            this.appLabel = appLabel;
            this.context = context;
            this.entryImpInput = new SourcePath("src\\Checked\\Nucleus\\Main\\Entry.imp.beat");
            SourcePath mainBeatSrc = new SourcePath("src\\Checked\\Nucleus\\Main\\Main.ifc.beat");
            this.mainBeatVerb = new BeatVerb(context, mainBeatSrc, appLabel);
            this.genericStitch = new SourcePath("src\\Trusted\\Spec\\Entry.ifc.basm.stitch");
            this.appSpecificStitch = new SourcePath(string.Format("src\\Trusted\\Spec\\{0}\\AppRequirements.ifc.stitch", appLabel));
        }

        public override AbstractId getAbstractIdentifier()
        {
            return new AbstractId(this.GetType().Name, version, this.genericStitch.ToString(), concrete: this.appLabel);
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;

            OrderPreservingSet<BuildObject> deps = new OrderPreservingSet<BuildObject>();

            // Things we need to stitch the interface:
            deps.Add(this.genericStitch);
            deps.Add(this.appSpecificStitch);
            deps.AddRange(this.mainBeatVerb.getOutputs());

            // Things we need to stitch the imports into the imp file:
            deps.Add(this.entryImpInput);
            deps.Add(this.context.getContextOutput());
            IIncludePathContext pathContext = this.context.fetchIfAvailable(ref ddisp);
            if (pathContext != null)
            {
                this.dafnyMainIfcInput = pathContext.search("dafny_Main_i", ModPart.Ifc);
                Util.Assert(this.dafnyMainIfcInput != null);
                deps.Add(this.dafnyMainIfcInput);
                this.dafnyMainImpInput = pathContext.search("dafny_Main_i", ModPart.Ifc);
                Util.Assert(this.dafnyMainImpInput != null);
                deps.Add(this.dafnyMainImpInput);
            }

            return deps;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { this.mainBeatVerb, this.context };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { this.getIfcOutput(), this.getEntryImpOutput() };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            // Mimic this line from src\Checked\Nucleus\Main\build.ps1:
            // _cat -out $OBJ\EntryCP_i.bpl -in $OBJ\MainCP_i.bpl,$SPEC_OBJ\EntryCP_i.bpl
            // TODO: eliminate this special-case workaround.
            try
            {
                // This is the trusted bit, creating the stitched ifc file.
                ////IEnumerable<string> ifcImports = extractImportStatements(dafnyMainIfcInput);
                string[] mainLines = File.ReadAllLines(workingDirectory.PathTo(this.mainBeatVerb.getOutputs().First()));
                string[] entryLines = File.ReadAllLines(workingDirectory.PathTo(this.genericStitch));
                int sentinel_index = Array.IndexOf(entryLines, SENTINEL_APP_SPECIFIC_GOES_HERE);
                if (sentinel_index < 0)
                {
                    throw new UserError("Sentinel string missing in " + this.genericStitch);
                }

                IEnumerable<string> entryPrologue = entryLines.Take(sentinel_index + 1);
                IEnumerable<string> entryEpilogue = entryLines.Skip(sentinel_index + 1);
                string[] appSpecificLines = File.ReadAllLines(workingDirectory.PathTo(this.appSpecificStitch));
                ////File.WriteAllLines(getIfcOutput().getFilesystemPath(), ifcImports.Concat(mainLines.Concat(entryLines)));
                File.WriteAllLines(
                    workingDirectory.PathTo(this.getIfcOutput()),
                    mainLines.Concat(entryPrologue).Concat(appSpecificLines).Concat(entryEpilogue));

                // Here's some (at least untrusted) workaround, snarfing and repurposing the
                // import list from dafny_Main_i up to Entry.imp.
                IEnumerable<string> impImports = extractImportStatements(workingDirectory, this.dafnyMainImpInput);
                string[] intext = File.ReadAllLines(workingDirectory.PathTo(this.entryImpInput));
                File.WriteAllLines(workingDirectory.PathTo(this.getEntryImpOutput()), impImports.Concat(intext));

                return new VerbSyncWorker(workingDirectory, new Fresh());
            }
            catch (IOException ex)
            {
                return new VerbSyncWorker(workingDirectory, new Failed(ex.ToString()));
            }
        }

        // We also have to stitch the imp, to borrow the private-import list from dafny_Main.
        internal BuildObject getEntryImpOutput()
        {
            return new SourcePath("src\\Checked\\Nucleus\\Main\\EntryStitched.x").makeLabeledOutputObject(this.appLabel, BeatExtensions.BEATIMP_EXTN);
        }

        private static IEnumerable<string> extractImportStatements(WorkingDirectory workingDirectory, BuildObject obj)
        {
            // Well, it might be nice to use BeatExtensions.propagatePrivateImports, but that requires
            // a context to interpret the input imports. We don't really want to cons up yet ANOTHER
            // intermediate context, so here's a temporary workaround.  Caution; may be brittle.
            IEnumerable<string> imports = File.ReadAllLines(workingDirectory.PathTo(obj))
                .Where(line => line.Contains("private-import"));

            // Note that dafny_Main_i didn't really expect us to steal its
            // imports, so it hasn't conditioned the Checked and Trusted imports to be beat-resistant.
            imports = imports.Select(
                line => line.Contains("Checked") || line.Contains("Trusted")
                ? line.Replace("private-import", "private-basmonly-import")
                : line);
            return imports;
        }

        private BuildObject getIfcOutput()
        {
            // TODO will probably require parameterization per app
            return new SourcePath("src\\Trusted\\Spec\\EntryStitched.x").makeLabeledOutputObject(this.appLabel, BoogieAsmVerifyVerb.BASMIFC_EXTN);
        }
    }
}
