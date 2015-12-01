
namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    using NDepend.Path;

    class FStarFindDepsResult : VirtualContents
    {
        public readonly OrderPreservingSet<BuildObject> Value;

        public FStarFindDepsResult(string output, WorkingDirectory workDir)
        {
            this.Value = this.ParseOutput(output, workDir);
        }

        private OrderPreservingSet<BuildObject> ParseOutput(string output, WorkingDirectory workDir)
        {
            var stdDeps = FStarEnvironment.getStandardDependencies();
            var set = new OrderPreservingSet<BuildObject>();
            var entries = output.Split(new[] { '\n' }, StringSplitOptions.RemoveEmptyEntries).ToList();
            // the final item is always the input file.
            //var inputFile = entries[entries.Count - 1];
            entries.RemoveAt(entries.Count - 1);
            // we need to search for dependencies that refer to files that come with the F* distribution to ensure that NuBuild handles those dependencies properly.
            foreach (var entry in entries)
            {
                var relFilePath = FilePath.AbsoluteToNuBuild(entry.ToAbsoluteFilePath(), workDir);
                BuildObject foundStdDep = null;
                foreach (var stdDep in stdDeps)
                {
                    var s0 = stdDep.toRelativeFilePath().ToString();
                    var s1 = relFilePath.ToString();
                    if (s0.Equals(s1, StringComparison.InvariantCultureIgnoreCase))
                    {
                        foundStdDep = stdDep;
                        break;
                    }
                }
                set.Add(foundStdDep ?? new BuildObject(relFilePath.ToString()));
            }
            return set;
        }
    }
}
