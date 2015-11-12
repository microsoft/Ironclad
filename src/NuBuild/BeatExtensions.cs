//--
// <copyright file="BeatExtensions.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;
    using System.Text;

    public enum ModPart
    {
        Ifc,
        Imp,
        Unknown
    }

    public static class ModPartExtensions
    {
        public const string ModPartIfc = ".ifc";
        public const string ModPartImp = ".imp";
        public const string ModPartUnknown = ".unk";

        public static string ExtnStr(this ModPart modPart)
        {
            switch (modPart)
            {
                case ModPart.Ifc: return ModPartIfc;
                case ModPart.Imp: return ModPartImp;
                case ModPart.Unknown: return ModPartUnknown;
                default: return null;
            }
        }
    }

    internal class BeatExtensions
    {
        public const string BEAT_EXTN = ".beat";
        public const string BEATIFC_EXTN = ".ifc.beat";
        public const string BEATIMP_EXTN = ".imp.beat";

        public static ModPart whichPart(string filenameOrExtn)
        {
            string modPartStr = "." + filenameOrExtn.Split('.')[1];
            switch (modPartStr)
            {
                case ModPartExtensions.ModPartIfc: return ModPart.Ifc;
                case ModPartExtensions.ModPartImp: return ModPart.Imp;
                default: return ModPart.Unknown;
            }
        }

        public static BuildObject makeOutputObject(BuildObject input, string typeExtn)
        {
            return makeLabeledOutputObject(input, null, typeExtn);
        }

        internal static BuildObject makeLabeledOutputObject(BuildObject input, string appLabel, string typeExtn)
        {
            ModPart part = whichPart(input);
            if (part == ModPart.Unknown)
            {
                // Input must be a raw boogie file.
                Util.Assert(input.getExtension().EndsWith(BoogieVerb.BPL_EXTN));
                return input.makeLabeledOutputObject(appLabel, typeExtn);
            }
            else
            {
                return input.makeLabeledOutputObject(appLabel, part.ExtnStr() + typeExtn);
            }
        }

        public static ModPart whichPart(BuildObject obj)
        {
            return whichPart(obj.getExtension());
        }

        private static IEnumerable<BeatIncludes.LabeledInclude> getBeatFlavoredShallowIncludesLabeled(
            IContextGeneratingVerb contextVerb, BuildObject rootObj)
        {
            ContextContents context = (ContextContents)
                BuildEngine.theEngine.Repository.FetchVirtual(contextVerb.getContextOutput());
            BeatIncludes includes = new BeatIncludes(context.Context);
            OrderPreservingSet<BeatIncludes.LabeledInclude> result = new OrderPreservingSet<BeatIncludes.LabeledInclude>(
                includes.getLabeledIncludes(rootObj));

            if (BeatExtensions.whichPart(rootObj) == ModPart.Imp)
            {
                BuildObject rootIfc = context.Context.search(rootObj.getFileNameWithoutExtension(), ModPart.Ifc);
                result.Add(new BeatIncludes.LabeledInclude(BeatIncludes.ImportFilter.ForBeatOrBasm, rootIfc));
            }

            return result;
        }

        public static IEnumerable<BuildObject> getBeatFlavoredShallowIncludes(
            IContextGeneratingVerb contextVerb, BuildObject rootObj, BeatIncludes.ImportFilter importFilter)
        {
            return getBeatFlavoredShallowIncludesLabeled(contextVerb, rootObj)
                .Where(li => importFilter == BeatIncludes.ImportFilter.ForBasmOnly
                    || li.importFilter == BeatIncludes.ImportFilter.ForBeatOrBasm)
                .Select(li => li.buildObject);
        }

        public static void propagatePrivateImports(
            WorkingDirectory workingDirectory,
            IContextGeneratingVerb contextVerb,
            BuildObject srcobj,
            BuildObject dstobj)
        {
            // Rewrite basm output to propagate any import statements from the beat file.
            // TODO this step really should be a beat function, not part of the build system.
            IEnumerable<BeatIncludes.LabeledInclude> beatImports =
                getBeatFlavoredShallowIncludesLabeled(contextVerb, srcobj);
            StringBuilder sb = new StringBuilder();
            foreach (BeatIncludes.LabeledInclude li in beatImports)
            {
                sb.Append("//-");
                sb.Append(li.importFilter == BeatIncludes.ImportFilter.ForBasmOnly
                    ? "private-basmonly-import" : "private-import");
                sb.Append(" ");
                sb.Append(li.buildObject.getFileNameWithoutExtension());
                sb.AppendLine(";");
            }

            // REVIEW: Improve upon this round-about way of prepending to a file?
            string beatOutput = File.ReadAllText(workingDirectory.PathTo(dstobj));
            File.Delete(workingDirectory.PathTo(dstobj));
            File.WriteAllText(workingDirectory.PathTo(dstobj), sb.ToString() + beatOutput);
        }

        // This used to use a BeatTransitiveDepsVerb, but we're going with shallow dependencies at the moment.
        // We may want to restore that behavior later, if we can get some sane transitive dep tree worked out for
        // Verve code.
        // The returned list belongs to the caller to .Add() to as desired.
        // TODO this really needs to be factored to supply the actual Beat-flavored references separately
        // from the auxiliary deps (transitive dep objects and context dep objects), so we don't have
        // client code trying to filter back out the part it wants. Brittle.
        public static OrderPreservingSet<BuildObject> getBeatFlavoredShallowDependencies(
            IContextGeneratingVerb contextVerb, BuildObject rootObj, out DependencyDisposition ddisp, BeatIncludes.ImportFilter filter)
        {
            OrderPreservingSet<BuildObject> result = new OrderPreservingSet<BuildObject>();
            result.Add(contextVerb.getContextOutput());
            try
            {
                result.AddRange(getBeatFlavoredShallowIncludes(contextVerb, rootObj, filter));
                ddisp = DependencyDisposition.Complete;
            }
            catch (ObjectNotReadyException)
            {
                ddisp = DependencyDisposition.Incomplete;
            }
            catch (ObjectFailedException)
            {
                ddisp = DependencyDisposition.Failed;
            }

            result.Add(rootObj);    // root really needs to go at the end of the list.
            return result;
        }

        public static BasmTransitiveDepsVerb getBasmFlavoredTransitiveDepVerb(IContextGeneratingVerb context, BuildObject rootObj)
        {
            return new BasmTransitiveDepsVerb(context, rootObj);
        }

        // The list belongs to the caller to .Add() to as desired.
        public static OrderPreservingSet<BuildObject> getBasmFlavoredTransitiveDependencies(IContextGeneratingVerb context, BuildObject rootObj, out DependencyDisposition ddisp)
        {
            OrderPreservingSet<BuildObject> result = new OrderPreservingSet<BuildObject>();
            TransitiveDepsVerb depsVerb = getBasmFlavoredTransitiveDepVerb(context, rootObj);
            result.Add(depsVerb.depsObj());
            result.AddRange(depsVerb.getAvailableDeps(out ddisp));

            // NB add root object at end of list, to keep it in definition-dependency order.
            result.Add(rootObj);
            return result;
        }
    }
}
