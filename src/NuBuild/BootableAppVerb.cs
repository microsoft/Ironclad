//--
// <copyright file="BootableAppVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    // Needs to:
    // 1) Build the bootloader into pxeloader
    // 2) Build two IroncladApps: Loader and specified app
    //    Do this via a Batch
    // 3) Create a boot.ini

    internal class BootableAppVerb
        : Verb
    {
        ////public const string BOOT_EXTN = ".ini";
        public const string LOADER_DFY = "src\\Dafny\\Apps\\AppLoader\\Main.i.dfy";
        private const int version = 4;

        private SourcePath dfyroot;  // REVIEW: Never used?
        private AbstractId abstractId;
        private VerificationRequest verificationRequest;

        // Dependencies
        ////BuildObject bootloader = new BuildObject("obj\\Trusted\\BootLoader\\pxe-loader");   // TODO: Build this with the NMake verb!
        private BuildObject bootloader = new SourcePath("obj\\Trusted\\BootLoader\\pxe-loader", SourcePath.SourceType.PrebakedObjExpediency);

        // Outputs
        private BuildObject bootIniFile;
        private BuildObject loaderCopy;
        private BuildObject bootloaderCopy;
        private BuildObject appExecutableCopy;

        // Intermediate verbs
        private IroncladAppVerb loaderVerb;
        private IroncladAppVerb appVerb;
        private BatchVerifyVerb batchVerb;
        private VerificationResultSummaryVerb batchSummaryVerb;

        public BootableAppVerb(SourcePath dfyroot, DafnyCCVerb.FramePointerMode useFramePointer, VerificationRequest verificationRequest)
        {
            this.dfyroot = dfyroot;
            this.verificationRequest = verificationRequest;
            string concreteId = verificationRequest.ToString() + "," + useFramePointer.ToString();
            this.abstractId = new AbstractId(this.GetType().Name, version, dfyroot.ToString(), concrete: concreteId);

            string targetDirectory = Path.Combine(
                BuildEngine.theEngine.getObjRoot(),
                dfyroot.getDirPath(),
                "bootable-" + verificationRequest.ToString());
            this.bootIniFile = new BuildObject(Path.Combine(targetDirectory, "safeos\\boot.ini"));

            // TODO: Create the bootloader verb.

            this.loaderVerb = new IroncladAppVerb(new SourcePath(LOADER_DFY), IroncladAppVerb.TARGET.BARE_METAL, useFramePointer, verificationRequest);
            this.appVerb = new IroncladAppVerb(dfyroot, IroncladAppVerb.TARGET.BARE_METAL, useFramePointer, verificationRequest);

            this.batchVerb = new BatchVerifyVerb(dfyroot, new HashSet<IObligationsProducer>() { this.appVerb, this.loaderVerb }, BatchVerifyVerb.BatchMode.APP);
            this.batchSummaryVerb = new VerificationResultSummaryVerb(this.batchVerb);

            this.loaderCopy = new BuildObject(Path.Combine(targetDirectory, this.targetExecutableName(this.loaderVerb)));
            this.bootloaderCopy = new BuildObject(Path.Combine(targetDirectory, this.bootloader.getFileName()));
            this.appExecutableCopy = new BuildObject(Path.Combine(targetDirectory, this.targetExecutableName(this.appVerb)));
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            List<BuildObject> result = new List<BuildObject>();
            ////result.Add(this.bootloader);  // TODO: Replace with the bootloader verbs's output.
            result.Add(this.loaderVerb.getExe());
            result.Add(this.appVerb.getExe());

            result.AddRange(this.batchSummaryVerb.getOutputs());

            ddisp = DependencyDisposition.Complete;
            return result;
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            if (this.verificationRequest.isComplete())
            {
                VerificationResult vr = VerificationResult.fromXmlFile(this.batchSummaryVerb.getOutputFile());

                if (!vr.pass)
                {
                    Util.Assert(false);     // Should never get here, since Ironclad app should fail before producing a verified exe.
                    return new VerbSyncWorker(workingDirectory, new Failed());
                }
            }

            // Copy the AppLoader binary and the bootloader into the same directory as the app's binary, so the pxe-loader can find them.
            // REVIEW: Not clear this is doing the right thing with shift to WorkingDirectory.
            File.Copy(workingDirectory.PathTo(this.loaderVerb.getExe()), workingDirectory.PathTo(this.loaderCopy), true);
            File.Copy(workingDirectory.PathTo(this.appVerb.getExe()), workingDirectory.PathTo(this.appExecutableCopy), true);
            File.Copy(workingDirectory.PathTo(this.bootloader), workingDirectory.PathTo(this.bootloaderCopy), true);

            this.writeBootFile(workingDirectory);
            return new VerbSyncWorker(workingDirectory, new Fresh());
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            List<IVerb> result = new List<IVerb>();
            ////result.Add(bootloaderVerb);             // TODO when we're building the bootloader as part of NuBuild.
            result.Add(this.batchSummaryVerb);
            result.Add(this.appVerb);
            result.Add(this.loaderVerb);

            return result;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { this.bootIniFile, this.loaderCopy, this.bootloaderCopy };
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override Presentation getPresentation()
        {
            return this.batchSummaryVerb.getPresentation();
        }

        private string targetExecutableName(IroncladAppVerb fromVerb)
        {
            // It's okay that we're saving an unverified binary to a .exe extension, because it's
            // getting placed inside targetDirectory, which is labeled "bootable-unverified."
            return fromVerb.getAppLabel() + IroncladAppVerb.TRUSTED_EXE_EXTN;
        }

        // TODO: Rename obj to something meaningful.  Is it a boot file?
        private string mkBootFileEntry(WorkingDirectory workingDirectory, BuildObject obj)
        {
            return string.Format("Size={0}   Path=/{1}", new FileInfo(workingDirectory.PathTo(obj)).Length, obj.getFileName());
        }

        private void writeBootFile(WorkingDirectory workingDirectory)
        {
            List<string> lines = new List<string>();

            lines.Add(this.mkBootFileEntry(workingDirectory, this.loaderCopy));
            lines.Add(this.mkBootFileEntry(workingDirectory, this.appExecutableCopy));

            File.WriteAllLines(workingDirectory.PathTo(this.bootIniFile), lines);
        }
    }
}
