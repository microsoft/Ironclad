//--
// <copyright file="BoogieAsmDepBase.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics;
    using System.IO;
    using System.Linq;

    internal abstract class BoogieAsmDepBase
            : Verb
    {
        public const string BASM_EXTN = ".basm";
        public const string BASMIFC_EXTN = ".ifc.basm";
        public const string BASMIMP_EXTN = ".imp.basm";
        public const string CommentSymbol = "//";

        protected static NmakeVerb boogieAsmBuildExecutableVerb = new NmakeVerb(new SourcePath("tools\\BoogieAsm\\makefile", SourcePath.SourceType.Tools));

        protected IContextGeneratingVerb context;
        protected BuildObject basmInput;
        protected BuildObject upstreamObj;

        private const int version = 20;
        private AbstractId abstractId = null;

        public BoogieAsmDepBase(IContextGeneratingVerb context, BuildObject input)
        {
            this.context = context;
            this.upstreamObj = input;
            this.basmInput = computeBasmInput(context.getPoundDefines(), input);
        }

        public static bool isBasm(BuildObject obj)
        {
            return obj.getExtension().Equals(BASMIFC_EXTN)
                || obj.getExtension().Equals(BASMIMP_EXTN);
        }

        public abstract BuildObject outputFile();

        protected abstract int getVersion();

        protected abstract bool includeAllImps();

        protected virtual string getExtraAbstractID()
        {
            return string.Empty;
        }

        protected static BuildObject getBoogieasmExecutable()
        {
            return new BuildObject(Path.Combine(boogieAsmBuildExecutableVerb.getOutputPath().getRelativePath(), "boogieasm.exe"));
        }

        protected virtual IEnumerable<BuildObject> getExtraDeps(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return new BuildObject[] { };
        }

        public static BuildObject computeBasmInput(PoundDefines poundDefines, BuildObject upstreamObj)
        {
            if (BoogieAsmDepBase.isBasm(upstreamObj))
            {
                // We'll be reading upstreamObj directly. Don't makeOutputObject,
                // because it may well be a source file.
                return upstreamObj;
            }

            return BeatExtensions.makeLabeledOutputObject(upstreamObj, poundDefines.ToString(), BASM_EXTN);
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { outputFile() };
        }

        public override AbstractId getAbstractIdentifier()
        {
            if (this.abstractId == null)
            {
                this.abstractId = new AbstractId(this.GetType().Name, getVersion() + version, this.upstreamObj.ToString(), context.getPoundDefines(), getExtraAbstractID());
            }

            return abstractId;
        }

        internal class BasmModuleAccumulator
        {
            private IContextGeneratingVerb _contextGenVerb;
            private HashSet<IVerb> _mutableVerbSet;
            private OrderPreservingSet<BuildObject> _basmModules;   // these are the bits we want to pass in as Execute() arguments
            private HashSet<BuildObject> _auxiliaryDeps;    // these plus modules are the deps we need to wait on. We need these to get the right .tdeps.
            private IIncludePathContext context;
            private DependencyDisposition _ddisp;

            public IEnumerable<IVerb> verbs
            {
                get { return _mutableVerbSet; }
            }

            public IEnumerable<BuildObject> basmModules
            {
                get { return _basmModules; }
            }

            public IEnumerable<BuildObject> getDeps()
            {
                return _auxiliaryDeps.Concat(_basmModules);
            }

            public DependencyDisposition ddisp
            {
                get { return _ddisp; }
            }

            public BasmModuleAccumulator(IContextGeneratingVerb contextGenVerb, BuildObject upstreamObj, bool linkMode)
            {
                this._contextGenVerb = contextGenVerb;
                this._mutableVerbSet = new HashSet<IVerb>();

                // NB preserve module definition-dependency order.
                this._basmModules = new OrderPreservingSet<BuildObject>();
                this._auxiliaryDeps = new HashSet<BuildObject>();
                _ddisp = DependencyDisposition.Complete;

                ////try
                ////{
                _mutableVerbSet.Add(contextGenVerb);
                _auxiliaryDeps.UnionWith(contextGenVerb.getOutputs());

                context = contextGenVerb.fetchIfAvailable(ref _ddisp);

                if (context != null)
                {
                    OrderPreservingSet<BuildObject> deps;
                    if (!linkMode)
                    {
                        deps = BeatExtensions.getBeatFlavoredShallowDependencies(
                            contextGenVerb, upstreamObj, out _ddisp, BeatIncludes.ImportFilter.ForBasmOnly);
                    }
                    else
                    {
                        deps = BeatExtensions.getBasmFlavoredTransitiveDependencies(contextGenVerb, upstreamObj, out _ddisp);
                        _mutableVerbSet.Add(BeatExtensions.getBasmFlavoredTransitiveDepVerb(_contextGenVerb, upstreamObj));
                    }

                    // REVIEW: The following two variables are unused.  Remove?
                    string targetModName = upstreamObj.getFileNameWithoutExtension();
                    ModPart targetModPart = BeatExtensions.whichPart(upstreamObj);

                    // NB security policy note: When verifying X.imp, we must be sure to supply X.ifc
                    // to BoogieAsm, so that we know that we're actually verifying the promises
                    // that other modules are relying on when they say "X" (which is how X got on
                    // the verification obligation list). That property happens automatically here,
                    // because we make a list of modules (ignoring ifc/imp part), such as {A,B,X},
                    // and include *every* .ifc. If we're verifying X.imp, a conditional test
                    // includes it at the time we consider module X.

                    foreach (BuildObject dep in deps)
                    {
                        string depExtn = dep.getExtension();
                        if (depExtn == null
                            || depExtn.EndsWith(TransitiveDepsVerb.TDEP_EXTN)
                            || depExtn.EndsWith(ContextGeneratingVerb.CONTEXT_EXTN))
                        {
                            _auxiliaryDeps.Add(dep);
                        }
                        else
                        {
                            Util.Assert(depExtn.Equals(BeatExtensions.BEATIFC_EXTN)
                                || depExtn.Equals(BeatExtensions.BEATIMP_EXTN)
                                || depExtn.Equals(BASMIFC_EXTN)
                                || depExtn.Equals(BASMIMP_EXTN));   // Burned too many times by this silly filter-out strategy.
                            string modName = dep.getFileNameWithoutExtension();
                            ModPart modPart = BeatExtensions.whichPart(dep);
                            getBasmModule(modName, ModPart.Ifc);
                            if ((dep.Equals(upstreamObj) && modPart == ModPart.Imp) || linkMode)
                            {
                                getBasmModule(modName, ModPart.Imp);
                            }
                        }
                    }
                }

                ////}
                ////catch (ObjNotReadyException)
                ////{
                ////    // oh, we don't even have the context object yet.
                ////    _ddisp = DependencyDisposition.Incomplete;
                ////}
                ////catch (ObjFailedException)
                ////{
                ////    _ddisp = DependencyDisposition.Failed;
                ////}
            }

            private BuildObject maybeBeat(BuildObject obj, HashSet<IVerb> mutableVerbSet)
            {
                BuildObject result = obj;
                if (BeatVerb.isBeat(obj))
                {
                    BeatVerb beatVerb = new BeatVerb(_contextGenVerb, obj, appLabel: null);
                    IEnumerable<BuildObject> beatOuts = beatVerb.getOutputs();
                    Util.Assert(beatOuts.Count() == 1);
                    mutableVerbSet.Add(beatVerb);
                    result = beatVerb.getOutputs().First();
                }
                else
                {
                    // No, this thing should already be ready to consume.
                    ////mutableVerbSet.Add(new BoogieAsmVerifyVerb(context, obj));
                }

                Util.Assert(BoogieAsmVerifyVerb.isBasm(result));
                return result;
            }

            private void getBasmModule(string modName, ModPart modPart)
            {
                ////Logger.WriteLine(string.Format("context {0} modName {1} modPart {2}", context, modName, modPart));
                ////BuildObject ifcObj = context.search(modName, modPart);
                BuildObject ifcObj = BuildEngine.theEngine.getHasher().search(context, modName, modPart);
                if (ifcObj == null)
                {
                    Util.Assert(false); // I'm not sure this case even occur anymore, since we guard the foreach on incomplete deps.
                    _ddisp = _ddisp.combine(DependencyDisposition.Incomplete);
                }
                else
                {
                    ifcObj = maybeBeat(ifcObj, _mutableVerbSet);
                    _basmModules.Add(ifcObj);
                }
            }
        }

        protected IEnumerable<BoogieVerb> getBoogieVerbs(VerificationRequest verificationRequest)
        {
            if (verificationRequest.verifyMode == VerificationRequest.VerifyMode.NoVerify)
            {
                return new BoogieVerb[] { };
            }

            BoogieAsmDepBase.BasmModuleAccumulator acc = new BoogieAsmDepBase.BasmModuleAccumulator(context, upstreamObj, includeAllImps());
            List<BuildObject> basmModules = new List<BuildObject>(acc.basmModules.Where(mod => !mod.IsTrusted));

            OrderPreservingSet<BoogieVerb> normal_Boogie = new OrderPreservingSet<BoogieVerb>();
            OrderPreservingSet<BoogieVerb> SymDiff_Boogie = new OrderPreservingSet<BoogieVerb>();

            foreach (BuildObject basmModule in basmModules)
            {
                if (verificationRequest.verifyMode == VerificationRequest.VerifyMode.SelectiveVerify
                    && !verificationRequest.selectiveVerifyModuleNames.Contains(basmModule.getFileNameWithoutExtension()))
                {
                    continue;
                }

                normal_Boogie.Add(new BoogieVerb(context, basmModule, symdiff: VerificationRequest.SymDiffMode.NoSymDiff));

                if (verificationRequest.getSymDiffMode() == VerificationRequest.SymDiffMode.UseSymDiff
                        && BoogieAsmVerifyVerb.needs_symdiff(basmModule))
                {
                    SymDiff_Boogie.Add(new BoogieVerb(context, basmModule, symdiff: VerificationRequest.SymDiffMode.UseSymDiff));
                }
            }

            return SymDiff_Boogie.Union(normal_Boogie);
        }

        protected IEnumerable<IVerb> getVerifyishVerbs()
        {
            // All the available things that make Beat or Basm ...
            BasmModuleAccumulator acc = new BasmModuleAccumulator(context, upstreamObj, includeAllImps());

            // Plus the transitive deps.
            IEnumerable<IVerb> extraDeps = new IVerb[] { context, boogieAsmBuildExecutableVerb };
            return acc.verbs.Concat(extraDeps).Concat(context.getVerbs());
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            BasmModuleAccumulator acc = new BasmModuleAccumulator(context, upstreamObj, includeAllImps());
            IEnumerable<BuildObject> result = acc.getDeps();
            DependencyDisposition ddisp_extra;
            IEnumerable<BuildObject> result_extra = getExtraDeps(out ddisp_extra);
            ddisp = acc.ddisp.combine(ddisp_extra);
            return result.Concat(result_extra).Concat(new[] { getBoogieasmExecutable() });
        }
    }
}
