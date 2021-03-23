//--
// <copyright file="TransitiveDepsVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    internal abstract class TransitiveDepsVerb
        : Verb
    {
        public const string TDEP_EXTN = ".tdep";
        private const int version = 3;

        private BuildObject obj;
        private BuildObject _depsObj;

        protected TransitiveDepsVerb(BuildObject obj)
        {
            this.obj = obj;
            this._depsObj = obj.makeVirtualObject(BeatExtensions.whichPart(obj).ExtnStr() + TDEP_EXTN);
        }

        public BuildObject depsObj()
        {
            return this._depsObj;
        }

        public override AbstractId getAbstractIdentifier()
        {
            return new AbstractId(this.GetType().Name, version, this.obj.getRelativePath());
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { this.depsObj() };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            OrderPreservingSet<BuildObject> shallowDeps = new OrderPreservingSet<BuildObject>();
            OrderPreservingSet<BuildObject> transitiveDeps = new OrderPreservingSet<BuildObject>();

            IEnumerable<BuildObject> includes = this.getIncludeFactory().getIncludes(this.obj);
            foreach (BuildObject child in includes)
            {
                shallowDeps.Add(child);
                transitiveDeps.AddRange(this.factory(child).getTransitiveIncludes());
                transitiveDeps.Add(child);
            }

            VirtualContents contents = new TransitiveDepsContents(shallowDeps, transitiveDeps);
            BuildEngine.theEngine.Repository.StoreVirtual(this.depsObj(), new Fresh(), contents);
            return new VerbSyncWorker(workingDirectory, new Fresh());
        }

        // Available only after this verb is Fresh.
        // These are called the "transitive includes" because from this point of view, these aren't
        // dependencies, they're the included files. The caller may be using them to describe
        // his dependencies, though.
        public IEnumerable<BuildObject> getTransitiveIncludes()
        {
            TransitiveDepsContents contents =
                (TransitiveDepsContents)BuildEngine.theEngine.Repository.FetchVirtual(this.depsObj());
            return contents.transitiveDeps;
        }

        public IEnumerable<BuildObject> getShallowIncludes()
        {
            TransitiveDepsContents contents =
                (TransitiveDepsContents)BuildEngine.theEngine.Repository.FetchVirtual(this.depsObj());
            return contents.shallowDeps;
        }

        // This is a helper method for the downstream verb's getDependencies().
        // It emits this verb's output token so that if this verb is
        // not yeat Fresh, the scheduler will strive to get this verb Executed,
        // plus if this verb is Fresh, tacks on all of the deps computed by
        // this verb.
        // The returned HashSet belongs to the caller, who is free
        // to stuff more into it.
        public HashSet<BuildObject> getAvailableDeps(out DependencyDisposition ddisp)
        {
            HashSet<BuildObject> result = new HashSet<BuildObject>();
            result.Add(this.depsObj());

            try
            {
                result.UnionWith(this.getTransitiveIncludes());
                result.Add(this.obj);    // Add this last, since BoogieAsmLinkVerb appears to depend on this ordering
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

            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            try
            {
                IEnumerable<BuildObject> includes = this.getIncludeFactory().getIncludes(this.obj);

                // NB evaluating eagerly so we can catch the exception here rather
                // than hide it in a lazy evaluation later.
                List<IVerb> result = new List<IVerb>(includes.Select(parent => this.factory(parent)));
                return result;
            }
            catch (ObjectNotReadyException)
            {
            }
            catch (SourceConfigurationError except)
            {
                throw new SourceConfigurationError(except.Message + " which is included by " + this.obj.getRelativePath());
            }

            return new IVerb[] { };
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            // NB we'll either return the singleton list {obj} if obj isn't yet available,
            // or we'll return the entire list of deps on obj's parents.
            List<BuildObject> deps = new List<BuildObject>();
            this.extendDeps(deps);
            deps.Add(this.obj);

            try
            {
                IEnumerable<BuildObject> includes = this.getIncludeFactory().getIncludes(this.obj);
                if (includes.Contains(this.obj))
                {
                    throw new SourceConfigurationError("Include loop starting at " + this.obj);
                }

                deps.AddRange(includes.Select(parent => this.factory(parent).depsObj()));
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

            return deps;
        }

        protected virtual void extendDeps(List<BuildObject> deps)
        {
        }

        protected abstract TransitiveDepsVerb factory(BuildObject obj);

        protected abstract IIncludeFactory getIncludeFactory();
   }
}
