//--
// <copyright file="BoogieAsmWorkerBase.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;
    using System.Text;
    using System.Threading.Tasks;

    internal abstract class BoogieAsmWorkerBase
        : BoogieAsmDepBase, IProcessInvokeAsyncVerb
    {
        public BoogieAsmWorkerBase(IContextGeneratingVerb context, BuildObject input)
            : base(context, input)
        {
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            List<string> args = new List<string>();
            //// args.add(BUILD_DEFS
            //// args.add(boogieasm_flags)
            args.Add(getAction());
            BuildObject captureStdout = null;
            if (outFlagWorks())
            {
                args.Add("-out");
                args.Add(outputFile().getRelativePath());
            }
            else
            {
                captureStdout = outputFile();
            }

            BasmModuleAccumulator acc = new BasmModuleAccumulator(context, upstreamObj, includeAllImps());
            Util.Assert(acc.ddisp == DependencyDisposition.Complete);
            args.AddRange(acc.basmModules.Select(module => module.getRelativePath()));
            args.AddRange(context.getPoundDefines().ToDefArgs());
            extendArgs(args);

            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                getBoogieasmExecutable().getRelativePath(),
                args.ToArray(),
                ProcessExitCodeHandling.NonzeroIsFailure,
                getDiagnosticsBase(),
                captureStdout: captureStdout);
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            postprocess(workingDirectory);
            return disposition;
        }

        protected abstract string getAction();

        protected abstract bool outFlagWorks(); // Weird that it works for -verify but not -link!

        protected virtual void extendArgs(List<string> args)
        {
        }

        protected virtual void postprocess(WorkingDirectory workingDirectory)
        {
        }
    }
}
