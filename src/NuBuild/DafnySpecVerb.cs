//--
// <copyright file="DafnySpecVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    internal class DafnySpecVerb
        : DafnyTransformBaseVerb
    {
        private AbstractId abstractId;
        private VSSolutionVerb dafnySpecBuildExecutableVerb;

        public DafnySpecVerb(SourcePath dfyroot, string appLabel)
            : base(dfyroot, appLabel)
        {
            this.abstractId = new AbstractId(this.GetType().Name, this.getVersion() + version, dfyroot.ToString());
            this.dafnySpecBuildExecutableVerb = new VSSolutionVerb(new SourcePath("tools\\DafnySpec\\DafnySpec.sln", SourcePath.SourceType.Tools));
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return base.getVerbs().Concat(new[] { this.dafnySpecBuildExecutableVerb });
        }

        protected override int getVersion()
        {
            return 15;
        }

        protected override BuildObject getExecutable()
        {
            return new BuildObject(Path.Combine(this.dafnySpecBuildExecutableVerb.getOutputPath().getRelativePath(), "dafnyspec.exe"));
        }

        protected override IEnumerable<BuildObject> getExtraDependencies()
        {
            string exePath = this.dafnySpecBuildExecutableVerb.getOutputPath().getRelativePath();

            // REVIEW: Should we extract the dafnyspec.exe dependencies from the project file instead of listing them manually?
            return new BuildObject[] {
                new BuildObject(Path.Combine(exePath, "DafnySpecAst.dll")),
                new BuildObject(Path.Combine(exePath, "Parser.dll")),
            };
        }

        protected override IEnumerable<SourcePath> getRoots()
        {
            // TODO why doesn't DafnyCC require DafnyPreludePath?
            return new SourcePath[] { this.getDafnyPrelude(), this.getSeqSpec(), dfyroot };
        }

        protected override bool transformFilterAccepts(BuildObject dfysource)
        {
            string fn = dfysource.getFileNameWithoutExtension();
            if (fn.EndsWith("." + DafnyTransformBaseVerb.DAFNY_S_SUFFIX))
            {
                return true;
            }
            else
            {
                Util.Assert(fn.EndsWith("." + DafnyTransformBaseVerb.DAFNY_I_SUFFIX) || fn.EndsWith("." + DafnyTransformBaseVerb.DAFNY_C_SUFFIX) || dfysource.Equals(this.getDafnyPrelude()));
                return false;
            }
        }

        protected override IEnumerable<SourcePath> getRootArgs()
        {
            OrderPreservingSet<SourcePath> specFiles = new OrderPreservingSet<SourcePath>();
            specFiles.Add(this.getDafnyPrelude());
            specFiles.Add(this.getSeqSpec());
            DependencyDisposition ddisp;
            foreach (SourcePath src in this.getAllDafnyModules(out ddisp))
            {
                if (this.transformFilterAccepts(src))
                {
                    specFiles.Add(src);
                }
            }

            return specFiles;
        }

        private SourcePath getSeqSpec()
        {
            return new SourcePath("src\\Trusted\\DafnySpec\\Seq.s.dfy");
        }
    }
}
