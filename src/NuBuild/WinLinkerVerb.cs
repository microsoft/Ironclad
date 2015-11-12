//--
// <copyright file="WinLinkerVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    internal class WinLinkerVerb : LinkerVerb
    {
        public const string WIN_APP_EXE_EXTN = ".winapp";
        private const int version = 6;

        public WinLinkerVerb(MasmVerb masmVerb, bool isLoader) : base(masmVerb, isLoader)
        {
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            // TODO: We shouldn't be using absolute paths to any of these things.
            // Change this to allow VS and SDKs to be installed anywhere.
            string linker = @"C:\Program Files (x86)\Microsoft Visual Studio 12.0\VC\bin\link.exe";
            string vc_lib_dir = @"C:\Program Files (x86)\Microsoft Visual Studio 12.0\VC\lib";
            string sdk_dir = @"C:\Program Files (x86)\Windows Kits\8.1\Lib\winv6.3\um\x86";
            string kernel_lib = @"C:\Program Files (x86)\Windows Kits\8.1\Lib\winv6.3\um\x86\kernel32.Lib";

            string standalone_support_lib = getStandaloneLib().getRelativePath();
            SourcePath zero1 = new SourcePath("tools\\scripts\\zero.obj", SourcePath.SourceType.Tools);
            SourcePath zero2 = new SourcePath("tools\\scripts\\zero2.obj", SourcePath.SourceType.Tools);

            // TODO: Fail more gracefully?  Or better yet, move these into iron/tools.
            if (!Directory.Exists(vc_lib_dir))
            {
                throw new FileNotFoundException("Missing Visual C++ library directory: " + vc_lib_dir);
            }

            if (!Directory.Exists(sdk_dir) || !File.Exists(kernel_lib))
            {
                throw new FileNotFoundException("Missing Windows SDK libraries: " + sdk_dir + ", " + kernel_lib + @". Try installing the Windows SDK from: \\research\Root\Products\Developers\Windows Driver Kit 8.1");
            }

            // TODO: Unpack/generate these automatically.
            // TODO: Brian, we're really not going to want to cache these big, empty sources. Or compress? All big (>10MB) files.
            // are mostly zeros.
            if (!File.Exists(IronRootDirectory.PathTo(zero1)) || !File.Exists(IronRootDirectory.PathTo(zero2)))
            {
                throw new FileNotFoundException("Missing object files of zeroes: " + zero1 + ", " + zero2 + ".  Try running: tools\\scripts\\build-standalone-init.sh");
            }

            List<string> args = new List<string>() { "/DEBUG", "/subsystem:console", "/LARGEADDRESSAWARE", "/fixed" };
            args.Add(objFile.getRelativePath());
            args.Add(zero1.getRelativePath());
            args.Add(zero2.getRelativePath());
            args.Add(standalone_support_lib);
            args.Add(@"""" + kernel_lib + @"""");
            args.Add("\"/libpath:" + vc_lib_dir + '"');
            args.Add("\"/libpath:" + sdk_dir + '"');
            args.Add("/out:" + outputObject.getRelativePath());
            args.Add("/entry:" + this.entryPoint);
            args.Add("/base:" + this.baseAddr);
            args.Add("/PDB:" + this.getPdb());

            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                linker,
                args.ToArray(),
                ProcessExitCodeHandling.NonzeroIsFailure,
                getDiagnosticsBase(),
                allowAbsoluteExe: true,
                allowAbsoluteArgs: true);
        }

        public override Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            // No cleanup to do.
            return disposition;
        }

        // TODO: We should build this!
        protected static SourcePath getStandaloneLib()
        {
            return new SourcePath("tools\\standalone\\Debug\\StandAloneSupport.lib", SourcePath.SourceType.Tools);
        }

        protected override IEnumerable<BuildObject> getExtraOutputs()
        {
            List<BuildObject> outputs = new List<BuildObject>();
            outputs.Add(this.getPdb());
            return outputs;
        }

        protected override string outputExtension()
        {
            return WIN_APP_EXE_EXTN + LinkerVerb.UNTRUSTED_EXE_EXTN;
        }

        protected override int getVersion()
        {
            return version;
        }

        protected override IEnumerable<BuildObject> getExtraDependencies()
        {
            return new List<BuildObject>() { getStandaloneLib() };
        }

        private BuildObject getPdb()
        {
            return objFile.makeOutputObject(".pdb");
        }
    }
}
