//--
// <copyright file="DafnyCompileOneVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics;
    using System.IO;

    /// <summary>
    /// Verb to compile Dafny source code to CSharp target.
    /// </summary>
    internal class DafnyCompileOneVerb : Verb, IProcessInvokeAsyncVerb
    {
        private const int Version = 10;

        private const string IntermediateSourceFilename = "ExpandedSource.dfy";
        private const string CSharpExt = ".cs";
        private readonly SourcePath input;
        private readonly BuildObject output;
        private readonly AbstractId abstractId;
        private readonly IVerb[] verbs;
        private readonly DafnyTransitiveDepsVerb transitiveDepsVerb;
        private List<BuildObject> dependencies;
        private SourcePath expandedSource;

        public DafnyCompileOneVerb(SourcePath input)
        {
            if (input == null)
            {
                throw new ArgumentNullException("input");
            }

            this.abstractId = new AbstractId(GetType().Name, Version, input.ToString());
            this.input = input;
            this.output = input.makeOutputObject(CSharpExt);
            this.transitiveDepsVerb = new DafnyTransitiveDepsVerb(input);
            this.verbs = new IVerb[] { this.transitiveDepsVerb };
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            if (this.dependencies == null)
            {
                DependencyDisposition dd;
                var dependencies = new List<BuildObject>();

                // This method's implementation is dependent upon transitiveDepsVerb being the only element of verbs.
                Trace.Assert(this.verbs.Length == 1 && this.verbs[0] is DafnyTransitiveDepsVerb);
                dependencies.AddRange(this.transitiveDepsVerb.getAvailableDeps(out dd));
                dependencies.AddRange(DafnyExecutableDependencies.getDafnyExecutableDependencies());
                if (dd != DependencyDisposition.Complete)
                {
                    ddisp = dd;

                    // Dependency resolution isn't complete yet and we don't want to cache the incomplete list.
                    return dependencies;
                }

                this.dependencies = dependencies;
            }

            Trace.Assert(this.dependencies != null);
            ddisp = DependencyDisposition.Complete;
            return this.dependencies;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return this.verbs;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new[] { this.output };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            // First expand our Dafny source file to inline all its includes.
            this.expandedSource = this.input.getNewSourcePath("ExpandedSource.dfy");
            DafnyIncludes dafnyIncludes = new DafnyIncludes();
            dafnyIncludes.ExpandDafny(workingDirectory, this.input, this.expandedSource);

            // Call Dafny.exe to compile Dafny source to CSharp target.
            var args = new[] { "/noVerify", "/spillTargetCode:1", "/compile:2", "/ironDafny", this.expandedSource.getRelativePath() };
            Console.WriteLine("expanded source: " + this.expandedSource.getRelativePath());
            ////Logger.WriteLine("arguments: " + String.Join(" ", args));
            return
                new ProcessInvokeAsyncWorker(
                    workingDirectory,
                    this,
                    DafnyExecutableDependencies.getDafnyExecutable().getRelativePath(),
                    args,
                    ProcessExitCodeHandling.NonzeroIsFailure,
                    getDiagnosticsBase(),
                    returnStandardOut: true,  // REVIEW: Doesn't appear to be needed.
                    returnStandardError: true,  // REVIEW: Doesn't appear to be needed.
                    allowCloudExecution: true);
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            var dis = disposition;

            string cSharpPath = Path.ChangeExtension(workingDirectory.PathTo(this.expandedSource), CSharpExt);
            if (!File.Exists(cSharpPath))
            {
                // Dafny has a bug where compilation fails but result code is still 0.
                dis = new Failed();
            }

            if (dis is Fresh)
            {
                this.RewriteCSharpFile(cSharpPath, workingDirectory.PathTo(this.output));
            }

            return dis;
        }

        private void RewriteCSharpFile(string inputPath, string outputPath)
        {
            using (TextWriter writer = new StreamWriter(outputPath))
            {
                // Compile a list of namespaces that require edits
                var namespaces = new Dictionary<string, string>();
                using (TextReader reader = new StreamReader(inputPath))
                {
                    string line;                    
                    System.Text.RegularExpressions.Regex pattern = new System.Text.RegularExpressions.Regex("namespace @_(\\d+)_([\\w_]+) {", System.Text.RegularExpressions.RegexOptions.Compiled);

                    while ((line = reader.ReadLine()) != null)
                    {
                        var result = pattern.Match(line);
                        if (result.Success) 
                        {
                            string old_name = "_" + result.Groups[1] + "_" + result.Groups[2];
                            string new_name = "_" + result.Groups[2];
                            namespaces.Add(old_name, new_name);
                        }
                    }
                }

                using (TextReader reader = new StreamReader(inputPath))
                {
                    string line;
                    while ((line = reader.ReadLine()) != null)
                    {
                        line = line.Replace(IntermediateSourceFilename, this.input.getFileName());
                        line = line.Replace("public class @__default {", "public partial class @__default {");
                        line = line.Replace("@#", "@");

                        // Temporary work-around.  ToDo: Remove this after Dafny is fixed.
                        line = line.Replace("public class ", "public partial class ");

                        // Another temporary work-around.  ToDo: Figure out better solution.
                        line = line.Replace("@_default_Main", "@IronfleetMain");

                        // Find a more efficient approach?
                        foreach (KeyValuePair<string, string> entry in namespaces) 
                        {
                            line = line.Replace(entry.Key, entry.Value);
                        }

                        writer.WriteLine(line);
                    }
                }
            }
        }
    }
}
