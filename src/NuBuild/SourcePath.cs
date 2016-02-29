//--
// <copyright file="SourcePath.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.IO;

    /// <summary>
    /// Representation of a source BuildObject.
    /// These are things which we expect to pre-exist, instead of built by us.
    /// </summary>
    public class SourcePath
        : BuildObject
    {
        /// <summary>
        /// The type of "source" this is.
        /// </summary>
        private SourceType sourceType;

        /// <summary>
        /// Initializes a new instance of the SourcePath class.
        /// </summary>
        /// <param name="inpath">
        /// Relative path to this object in the local filesystem.
        /// </param>
        /// <param name="sourceType">
        /// The type of "source" this is.
        /// </param>
        public SourcePath(string inpath, SourceType sourceType = SourceType.Src, Func<AbsoluteFileSystemPath, string> hashFunc = null)
            : base(inpath, hashFunc: hashFunc)
        {
            // Sanity checks.
            this.checkPrefix(sourceType, SourceType.PrebakedObjExpediency, "obj");   // TODO remove.

            this.sourceType = sourceType;
            this.IsTrusted = getRelativePath().StartsWith(
                Path.Combine(BuildEngine.theEngine.getSrcRoot(), BuildEngine.VerveTrustedSpecDir), StringComparison.OrdinalIgnoreCase);
        }

        /// <summary>
        /// Various types of "sources".
        /// </summary>
        public enum SourceType
        {
            /// <summary>
            /// Source file.
            /// </summary>
            Src,

            /// <summary>
            /// Tools (executables usually) that we don't build ourselves.
            /// </summary>
            Tools,

            /// <summary>
            /// Special purpose expediency.
            /// Used to point at bootloader, until we can get an nmake verb working. TODO remove.
            /// </summary>
            PrebakedObjExpediency
        }

        /// <summary>
        /// Gets the source type of this instance.
        /// </summary>
        public SourceType Type
        {
            get { return this.sourceType; }
        }

        /// <summary>
        /// Creates a new SourcePath, where the source type is the same as this
        /// SourcePath's, and the path is relative to the directory containing
        /// this SourcePath.
        /// </summary>
        /// <remarks>
        /// REVIEW: This should be renamed to MakeNewSourcePath to correspond
        /// with BuildObject
        /// </remarks>
        /// <param name="inpath">Relative path to the new object.</param>
        /// <returns>The new SourcePath.</returns>
        public SourcePath getNewSourcePath(string inpath)
        {
            return new SourcePath(Path.Combine(getDirPath(), inpath), this.sourceType);
        }

        /// <summary>
        /// Checks that the path prefix for this object is reasonable for the
        /// given source type.
        /// </summary>
        /// <param name="givenType">The given source type.</param>
        /// <param name="matchType">
        /// Source type the prefix parameter matches.
        /// </param>
        /// <param name="prefix">
        /// Prefix that paths of the matchType parameter should have.
        /// </param>
        private void checkPrefix(SourceType givenType, SourceType matchType, string prefix)
        {
            if (givenType == matchType)
            {
                if (!path.StartsWith(prefix, StringComparison.OrdinalIgnoreCase))
                {
                    throw new UserError(string.Format(
                        "Source path {0} should begin with {1}",
                        this.path,
                        prefix));
                }
            }
        }
    }
}
