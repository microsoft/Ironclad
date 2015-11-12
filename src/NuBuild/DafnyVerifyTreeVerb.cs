//--
// <copyright file="DafnyVerifyTreeVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    internal class DafnyVerifyTreeVerb
        : Verb, IObligationsProducer
    {
        private const int version = 30;

        private const string DFYTREE_EXTN = ".dfytree";

        private SourcePath displayRoot; // used only in labeling the output
        private BuildObject obligations;
        private AbstractId abstractId;

        public DafnyVerifyTreeVerb(SourcePath root)
        {
            this.displayRoot = root;
            this.obligations = root.makeOutputObject(DFYTREE_EXTN + VerificationObligationList.VOL_EXTN);
            this.abstractId = new AbstractId(this.GetType().Name, version, root.ToString());
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public BuildObject getObligationSet()
        {
            return this.obligations;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            HashSet<BuildObject> availableDeps = this.getAvailableDeps(out ddisp);

            List<BuildObject> true_deps = new List<BuildObject>();
            foreach (BuildObject dep in availableDeps)
            {
                if (dep.getExtension().EndsWith(DafnyVerifyOneVerb.DAFNY_EXTN))
                {
                    true_deps.Add(this.mkVerificationObject(dep));
                }
                else
                {
                    true_deps.Add(dep);
                }
            }

            return true_deps;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            // TODO cast below assumes dafny files are always source files.
            // That's easy enough to remedy in DafnyVerifyOneVerb ctor, but for
            // now, we continue assuming it.      
            // This will matter if we ever auto-generate a Dafny file.
            DependencyDisposition ddispDummy;
            IEnumerable<IVerb> result = this.getDafnyDependencies(out ddispDummy)
                .Select(dfysource => new DafnyVerifyOneVerb((SourcePath)dfysource))
                .Concat(new List<IVerb>() { new DafnyTransitiveDepsVerb(this.displayRoot) });

            return result;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new HashSet<BuildObject>() { this.obligations };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            IEnumerable<BuildObject> verificationResults = this.getVerbs()
                .Where(verb => verb is VerificationResultVerb)
                .Select(dfy_one => ((VerificationResultVerb)dfy_one).getOutputFile());
            VerificationObligationList vol = new VerificationObligationList(verificationResults);
            vol.store(workingDirectory, this.obligations);
            return new VerbSyncWorker(workingDirectory, new Fresh());
        }

        private BuildObject mkVerificationObject(BuildObject dfysource)
        {
            return dfysource.makeOutputObject(DafnyVerifyOneVerb.DAFNY_EXTN + VerificationResultVerb.VERIFICATION_RESULT_EXTN);
        }

        private HashSet<BuildObject> getAvailableDeps(out DependencyDisposition ddisp)
        {
            TransitiveDepsVerb depsVerb = new DafnyTransitiveDepsVerb(this.displayRoot);
            HashSet<BuildObject> availableDeps = depsVerb.getAvailableDeps(out ddisp);
            availableDeps.Add(this.displayRoot);  // TransitiveDeps *exclude* the root, so we need to add that in, too.
            return availableDeps;
        }

        private IEnumerable<BuildObject> getDafnyDependencies(out DependencyDisposition ddisp)
        {
            HashSet<BuildObject> result = this.getAvailableDeps(out ddisp);
            return result.Where(dep => dep.getExtension().EndsWith(DafnyVerifyOneVerb.DAFNY_EXTN));
        }
    }
}
