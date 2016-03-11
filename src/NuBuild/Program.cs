//--
// <copyright file="Program.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;
    using System.Linq.Expressions;

    internal class Program
    {
        private bool useCloudExecution;
        private BackgroundWorker backgroundWorker;
        private string[] args;
        private VerificationRequest verificationRequest = new VerificationRequest();

        private Program()
        {
            this.useCloudExecution = false;
            this.backgroundWorker = new BackgroundWorker();
        }

        static void Main(string[] args)
        {
            try
            {
                new Program().main(args);
            }
            finally
            {
                Logger.Flush();
            }
        }

        void usage(string msg)
        {
            Logger.WriteLine(msg);
            Logger.WriteLine(string.Format(
                "Usage: {0} [opts] [Verb Target]*",
                System.AppDomain.CurrentDomain.FriendlyName));
            throw new UserError("Invalid options");
        }

        List<IVerb> verbs = new List<IVerb>();
        string html_output = null;
        IroncladAppVerb.TARGET target_platform = IroncladAppVerb.TARGET.BARE_METAL;
        DafnyCCVerb.FramePointerMode useFramePointer = DafnyCCVerb.FramePointerMode.NoFramePointer;

        private bool releaseBuild = true;

        int argi;

        string takeArg(string expectedThing)
        {
            if (argi >= args.Count())
            {
                usage("Expected " + expectedThing);
            }

            string rc = args[argi];
            argi += 1;
            return rc;
        }

        IEnumerable<string> takeRemainingArgs()
        {
            IEnumerable<string> result = new List<string>();
            if (this.argi < args.Length)
            {
                int n = argi;
                result = (new ArraySegment<string>(args, n, args.Length - n)).Select(s => s.Trim());
                argi = args.Length;
            }
            return result;
        }
        
        SourcePath parseSourcePath(string s)
        {
            var relPath = RelativeFileSystemPath.Parse(s, permitImplicit: true);
            var boPath = relPath.MapToBuildObjectPath();
            return new SourcePath(boPath.ToString());
        }

        void parseArgs(string[] args)
        {
            this.args = args;
            argi = 0;
            var rootDirInitState = Tuple.Create((string)null, false);
            while (argi < args.Count())
            {
                string next = takeArg("option or verb");    // Should always succeed due to while condition.
                if (next.StartsWith("-"))
                {
                    if (next.Equals("--ironRoot"))
                    {
                        if (rootDirInitState.Item2)
                        {
                            usage("ironRoot set after use");
                        }

                        rootDirInitState = Tuple.Create(takeArg("value for ironRoot"), false);
                    }
                    else if (next.Equals("-j") || next.Equals("--jobs"))
                    {
                        NuBuildEnvironment.Options.ParallelJobs = Int32.Parse(takeArg("value for jobs"));
                    }
                    else if (next.Equals("--localcache"))
                    {
                        BuildEngine.theEngine.setLocalCache(takeArg("path for localcache"));
                    }
                    else if (next.ToLower().Equals("--cloudcache"))
                    {
                        NuBuildEnvironment.Options.UseCloudCache = true;
                    }
                    else if (next.ToLower().Equals("--no-cloudcache"))
                    {
                        NuBuildEnvironment.Options.UseCloudCache = false;
                    }
                    else if (next.Equals("--cloudexecution"))
                    {
                        this.useCloudExecution = true;
                    }
                    else if (next.ToLower().Equals("--verify"))
                    {
                        this.verificationRequest.verifyMode = VerificationRequest.VerifyMode.Verify;
                    }
                    else if (next.ToLower().Equals("--no-verify"))
                    {
                        this.verificationRequest.verifyMode = VerificationRequest.VerifyMode.NoVerify;
                    }
                    else if (next.ToLower().Equals("--no-symdiff"))
                    {
                        this.verificationRequest.verifyMode = VerificationRequest.VerifyMode.NoSymDiff;
                    }
                    else if (next.ToLower().Equals("--verify-select"))
                    {
                        this.verificationRequest.verifyMode = VerificationRequest.VerifyMode.SelectiveVerify;
                        this.verificationRequest.selectiveVerifyModuleNames.Add(takeArg("filename for selective-verify"));
                    }
                    else if (next.ToLower().Equals("--html"))
                    {
                        this.html_output = takeArg("filename for html report");
                    }
                    else if (next.ToLower().Equals("--windows"))
                    {
                        this.target_platform = IroncladAppVerb.TARGET.WINDOWS;
                    }
                    else if (next.ToLower().Equals("--useframepointer"))
                    {
                        this.useFramePointer = DafnyCCVerb.FramePointerMode.UseFramePointer;
                    }
                    else if (next.ToLower().Equals("--debug"))
                    {
                        this.releaseBuild = false;
                    }
                    else if (next.ToLower().Equals("--log-tag"))
                    {
                        var tag = takeArg("tag");
                        Logger.LogTag(tag);
                    }
                    else if (next.ToLower().Equals("--ignore-tag"))
                    {
                        var tag = takeArg("tag");
                        Logger.IgnoreTag(tag);
                    }
                    else if (next.Equals("--quiet", StringComparison.InvariantCultureIgnoreCase))
                    {
                        Logger.Quiet();
                    }
                    else if (next.Equals("--enforce-whitespace", StringComparison.InvariantCultureIgnoreCase))
                    {
                        NuBuildEnvironment.Options.EnforceWhitespace = true;
                    }
                    else
                    {
                        usage("unrecognized option " + next);
                    }
                }
                else
                {
                    string verb = next;

                    if (!rootDirInitState.Item2)
                    {
                        var p = rootDirInitState.Item1 == null ? null : rootDirInitState.Item1;
                        NuBuildEnvironment.initialize(p);
                        rootDirInitState = Tuple.Create(rootDirInitState.Item1, true);
                    }

                    if (verb.Equals("FStarVerifyTree", StringComparison.InvariantCultureIgnoreCase) ||
                        verb.Equals("FStarVerify", StringComparison.InvariantCultureIgnoreCase))
                    {
                        // FStarVerifyTree can accept multiple arguments, hence the following complexity.
                        var remainingArgs = this.takeRemainingArgs().ToList();
                        if (remainingArgs.Count < 1)
                        {
                            throw new UserError("The FStarVerifyTree verb requires at least one argument, specifying the NuBuild source file path.");
                        }
                        verbs.Add(new FStarVerifyTreeVerb(remainingArgs, NuBuildEnvironment.InvocationPath, strict: false));
                    }
                    else if (verb.Equals("FStarVerifyOne", StringComparison.InvariantCultureIgnoreCase))
                    {
                        // FStarVerifyTree can accept multiple arguments, hence the following complexity.
                        var remainingArgs = this.takeRemainingArgs().ToList();
                        if (remainingArgs.Count < 1)
                        {
                            throw new UserError("The FStarVerifyOne verb requires at least one argument, specifying the NuBuild source file path.");
                        }
                        verbs.Add(new FStarVerifyOneVerb(remainingArgs, NuBuildEnvironment.InvocationPath, strict: false));
                    }
                    else
                    {
                        string target = takeArg("verb-target");

                        if (verb.Equals("DafnyVerifyTree", StringComparison.InvariantCultureIgnoreCase))
                        {
                            verbs.Add(new VerificationResultSummaryVerb(new DafnyVerifyTreeVerb(this.parseSourcePath(target))));
                        }
                        else if (verb.Equals("BatchDafny", StringComparison.InvariantCultureIgnoreCase))
                        {
                            if (!target.EndsWith(".batch"))
                            {
                                usage("Batching expects a .batch file containing a list of .dfy files");
                            }

                            verbs.Add(new VerificationResultSummaryVerb(new BatchVerifyVerb(this.parseSourcePath(target), BatchVerifyVerb.BatchMode.DAFNY, this.verificationRequest, useFramePointer)));
                        }
                        else if (verb.Equals("BatchApps", StringComparison.InvariantCultureIgnoreCase))
                        {
                            if (!target.EndsWith(".batch"))
                            {
                                usage("Batching expects a .batch file containing a list of .dfy files");
                            }

                            verbs.Add(new VerificationResultSummaryVerb(new BatchVerifyVerb(this.parseSourcePath(target), BatchVerifyVerb.BatchMode.APP, this.verificationRequest, useFramePointer)));
                        }
                        else if (verb.Equals("Beat", StringComparison.InvariantCultureIgnoreCase))
                        {
                            verbs.Add(new BeatVerb(BuildEngine.theEngine.getVerveContextVerb(PoundDefines.empty()), this.parseSourcePath(target), appLabel: null));
                        }
                        else if (verb.Equals("Boogie", StringComparison.InvariantCultureIgnoreCase))
                        {
                            verbs.Add(new BoogieVerb(BuildEngine.theEngine.getVerveContextVerb(PoundDefines.empty()), this.parseSourcePath(target), symdiff: this.verificationRequest.getSymDiffMode()));
                        }
                        else if (verb.Equals("IroncladApp", StringComparison.InvariantCultureIgnoreCase))
                        {
                            verbs.Add(new IroncladAppVerb(this.parseSourcePath(target), target_platform, this.useFramePointer, this.verificationRequest));
                        }
                        else if (verb.Equals("IronfleetApp", StringComparison.InvariantCultureIgnoreCase))
                        {
                            verbs.Add(new IronfleetAppVerb(this.parseSourcePath(target), this.verificationRequest, this.releaseBuild));
                        }
                        else if (verb.Equals("DafnyCompileOne", StringComparison.InvariantCultureIgnoreCase))
                        {
                            verbs.Add(new DafnyCompileOneVerb(this.parseSourcePath(target)));
                        }
                        else if (verb.Equals("VSSolution", StringComparison.InvariantCultureIgnoreCase))
                        {
                            verbs.Add(new VSSolutionVerb(new SourcePath(target, SourcePath.SourceType.Tools)));
                        }
                        else if (verb.Equals("NMake", StringComparison.InvariantCultureIgnoreCase))
                        {
                            verbs.Add(new NmakeVerb(new SourcePath(target, SourcePath.SourceType.Tools)));
                        }
                        else if (verb.Equals("BootableApp", StringComparison.InvariantCultureIgnoreCase))
                        {
                            verbs.Add(new BootableAppVerb(this.parseSourcePath(target), this.useFramePointer, this.verificationRequest));
                        }
                        else
                        {
                            usage("Unknown verb " + verb);
                        }
                    }
                }
            }

            if (!rootDirInitState.Item2)
            {
                var p = rootDirInitState.Item1 == null ? null : rootDirInitState.Item1;
                NuBuildEnvironment.initialize(p);
            }
        }

        private IItemCache GetItemCache()
        {
            string localCacheDirectory = Path.Combine(
                BuildEngine.theEngine.getIronRoot(),
                BuildEngine.theEngine.getLocalCache());

            if (NuBuildEnvironment.Options.UseCloudCache)
            {
                try
                {
                    BuildEngine.theEngine.CloudCache = new ItemCacheCloud();

                    return new ItemCacheMultiplexer(
                        new ItemCacheLocal(localCacheDirectory),
                        BuildEngine.theEngine.CloudCache,
                        this.backgroundWorker);
                }
                catch (Microsoft.WindowsAzure.Storage.StorageException)
                {
                    // -
                    // This will handle the case of being disconnected
                    // at NuBuild launch time.
                    // -
                    Logger.WriteLine("Failed to create multiplexed cloud cache -- falling back to just local cache.");
                }
            }

            return new ItemCacheLocal(localCacheDirectory);
        }

        void logNubuildInvocation(string[] args)
        {
            Logger.WriteLine(string.Format("invoked as: {0} {1}",
                NuBuildEnvironment.getAssemblyPath(),
                string.Join(" ", args)), "verbose");
        }

        // NB this file is found in the default ironroot, since we
        // grab it before we parse your --ironroot argument.
        private const string NUBUILD_CONFIG = "nubuild.config";

        private IEnumerable<string> fetchConfigArgs()
        {
            string config_path =
                Path.Combine(Directory.GetCurrentDirectory(), NUBUILD_CONFIG);
            if (!File.Exists(config_path))
            {
                return new string[] { };
            }

            List<string> config_args = new List<string>();
            foreach (string line in File.ReadAllLines(config_path))
            {
                foreach (string word in line.Trim().Split(new char[] { ' ' }))
                {
                    config_args.Add(word);
                }
            }

            return config_args;
        }

        void main(string[] cmdline_args)
        {
            string[] all_args = fetchConfigArgs().Concat(cmdline_args).ToArray();
            logNubuildInvocation(all_args);
            try
            {
                parseArgs(all_args);
            }
            catch (UserError err)
            {
                usage(err.Message);
            }

            BuildEngine.theEngine.ItemCache = GetItemCache();
            BuildEngine.theEngine.Repository = new Repository(BuildEngine.theEngine.ItemCache);
            if (this.useCloudExecution)
            {
                if (!NuBuildEnvironment.Options.UseCloudCache)
                {
                    usage("Cloud Execution requires Cloud Cache!");
                }

                BuildEngine.theEngine.CloudReportQueueName = Path.GetRandomFileName().Substring(0, 8);
                BuildEngine.theEngine.CloudExecutionQueue = new CloudExecutionQueue(BuildEngine.theEngine.CloudReportQueueName);
                Logger.WriteLine("Using cloud report queue name: " + BuildEngine.theEngine.CloudReportQueueName);
            }

            Scheduler scheduler = new Scheduler(NuBuildEnvironment.Options.ParallelJobs);

            scheduler.addTargetVerbs(verbs);

            ////try
            ////{
            scheduler.parallelSchedule();
            ////}
            ////catch (Exception ex)
            ////{
            ////    scheduler.dbgDisplayCounts();
            ////    throw;
            ////}

            IEnumerable<BuildObject> targets = scheduler.getTargets();

            BuildObject outputTarget = null;
            if (targets.Count() > 0)
            {
                outputTarget = targets.First();
            }
            else
            {
                Logger.WriteLine("No targets requested.");
            }

            if (targets.Count() > 1)
            {
                // TODO need a better story for relaying failure results. Right now
                // they get stuck in the results cache, but don't appear where we
                // can find them. Emit to a log, or to files in nuobj?
                Logger.WriteLine("Multiple targets build. First result follows.");
            }

            if (outputTarget != null)
            {
                Disposition d = scheduler.getObjectDisposition(outputTarget);
                if (d is Fresh)
                {
                    IVerb verb = scheduler.getParent(outputTarget);
                    Logger.Write(verb.getPresentation(), "summary");

                    if (this.html_output != null)
                    {
                        HTMLPresentater html = new HTMLPresentater();
                        verb.getPresentation().format(html);

                        try
                        {
                            using (StreamWriter sw = new StreamWriter(this.html_output))
                            {
                                sw.Write(html.ToString());
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.WriteLine("Failed to write html output to file: " + html_output);
                            Logger.WriteLine("Exception was: " + e);
                        }
                    }
                }
                else
                {
                    Logger.WriteLine("Build failed.");
                    foreach (string msg in d.getMessages())
                    {
                        Logger.WriteLine(msg);
                    }
                }
            }
            else if (targets.Count() == 0)
            {
                Logger.WriteLine("No targets requested.");
            }
            else
            {
                Logger.WriteLine("Multiple targets built. Look for results in nuobj/.");
            }

            // -
            // We have to explicitly ask the BackgroundWorker thread to exit
            // as it will prevent the process from exiting until it does.
            // -
            this.backgroundWorker.StopWork();

            // -
            // Report what the background worker accomplished during this run.
            // -
            this.backgroundWorker.WaitForCompletion();
            Logger.WriteLine(string.Format("Background Worker completed {0} work items out of {1} queued.",
                this.backgroundWorker.GetWorkItemsPerformed,
                this.backgroundWorker.GetWorkItemsQueued));
            if (this.backgroundWorker.GetWorkItemsFailed != 0)
            {
                Logger.WriteLine(string.Format(
                    "{0} work item procedures failed (threw an exception).",
                    this.backgroundWorker.GetWorkItemsFailed));
            }
        }
    }
}
