
namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    using NDepend.Path;

    class FStarFindDepsResult : VirtualContents
    {
        public readonly OrderPreservingSet<BuildObject> Value;

        public FStarFindDepsResult(string output)
        {
            this.Value = this.ParseOutput(output);
        }

        private OrderPreservingSet<BuildObject> ParseOutput(string output)
        {
            var set = new OrderPreservingSet<BuildObject>();
            var entries = output.Split(new[] { '\n' }, StringSplitOptions.RemoveEmptyEntries).ToList();
            // the final item is always the input file.
            entries.RemoveAt(entries.Count - 1);
            foreach (var entry in entries)
            {
                var relFilePath = FilePath.AbsoluteToNuBuild(entry.ToAbsoluteFilePath());
                set.Add(new BuildObject(relFilePath.ToString()));
            }
            return set;
        }
    }
}
