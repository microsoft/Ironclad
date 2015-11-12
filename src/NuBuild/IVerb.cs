//--
// <copyright file="IVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
using System;
using System.Collections.Generic;
using System.Xml;

    /// <summary>
    /// Definition of the interface to Verbs.
    /// </summary>
    internal interface IVerb
        : IComparable
    {
        /// <summary>
        /// Gets a possibly-incomplete list of things we depend on.
        /// </summary>
        /// <remarks><para>
        /// When the list is complete, it should cover every BuildObject
        /// this verb can see when running its worker's methods.
        /// That means that it's not safe, for example, to say
        /// "I only depend on my .exe and DafnyTransitiveDepsVerb(root).obj()".
        /// One might think so, since the Freshness of the latter implies that
        /// every object this verb needs is Fresh, but that doesn't convey
        /// what BuildObjects need to (potentially) be transmitted remotely for
        /// running the verb's worker's methods on a remote machine.
        /// </para><para>
        /// It should also cover any buildObjects needed to complete the list.
        /// That is, if the verb depends on a .tdep, and that .tdep is incomplete,
        /// the list should include that .tdep's partial dependency list, so
        /// the scheduler can figure out how to get it done.
        /// </para></remarks>
        /// <param name="ddisp">The returned DependencyDisposition.</param>
        /// <returns>
        /// A collection of build objects this verb depends upon.
        /// </returns>
        IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp);
        
        /// <summary>
        /// Gets a list of the verbs that can build the dependencies visible to
        /// getDependencies.  May return an incomplete list if getDependencies
        /// is incomplete.
        /// </summary>
        /// <returns>
        /// A collection of verbs that can build this verb's dependencies.
        /// </returns>
        IEnumerable<IVerb> getVerbs();
        
        /// <summary>
        /// Gets a list of the build objects this verb generates upon successful
        /// execution.
        /// </summary>
        /// <remarks>
        /// getOutputs is only meaningful once getDependencies indicates
        /// a complete disposition. The set of outputs doesn't change.
        /// </remarks>
        /// <returns>A collection of build objects built by this verb.</returns>
        IEnumerable<BuildObject> getOutputs();

        /// <summary>
        /// Gets the list of BuildObjects this verb generates containing
        /// diagnostic information. Diagnostics are never used as inputs
        /// by other verbs; they are only for the user's inspection.
        /// TODO: Rename to getDiagnosticOutputs().
        /// </summary>
        /// <returns>The collection of diagnostic BuildObjects.</returns>
        IEnumerable<BuildObject> getFailureOutputs();

        /// <summary>
        /// Gets an identifier that describes the verb up to differences in
        /// input.
        /// </summary>
        /// <remarks>
        /// This method must always be evaluable.
        /// Example:
        /// <code>DafnyVerifyOneVerb(SourcePath("src\\foo\\bar.dfy"))</code>
        /// </remarks>
        /// <returns>A unique identifier for the abstract verb.</returns>
        AbstractId getAbstractIdentifier();

        /// <summary>
        /// Gets a worker for this verb that performs this verb's work.
        /// </summary>
        /// <param name="workingDirectory">
        /// Working directory to use for this verb's execution.
        /// </param>
        /// <returns>A worker for this verb instance.</returns>
        IVerbWorker getWorker(WorkingDirectory workingDirectory);

        /// <summary>
        /// Gets a structured form of output UI for informing the user what
        /// happened.
        /// </summary>
        /// <returns>Something to present to the user.</returns>
        Presentation getPresentation();

        /// <summary>
        /// Gets a structured form of output UI for informing the user what is
        /// currently happening.
        /// </summary>
        /// <param name="disposition">
        /// The disposition of this verb's worker.
        /// </param>
        /// <returns>Something to present to the user.</returns>
        Presentation getRealtimePresentation(Disposition disposition);

        /// <summary>
        /// Writes an XML representation of this verb's CPU usage using the
        /// provided XmlWriter.
        /// </summary>
        /// <param name="xmlWriter">
        /// The XmlWriter to use to write the XML.
        /// </param>
        void writeTimingXml(XmlWriter xmlWriter);

        /// <summary>
        /// Writes an XML representation of this verb's internal state
        /// (for debugging purposes) using the provided XmlWriter.
        /// </summary>
        /// <param name="xmlWriter">
        /// The XmlWriter to use to write the XML.
        /// </param>
        void writeDebugXml(XmlWriter xmlWriter);
    }
}
