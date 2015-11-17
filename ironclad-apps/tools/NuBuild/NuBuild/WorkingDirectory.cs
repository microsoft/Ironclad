//--
// <copyright file="WorkingDirectory.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    /// <summary>
    /// A directory tree in the local filesystem for a verb to operate upon.
    /// Verbs should not access files outside of this directory tree.
    /// </summary>
    public class WorkingDirectory
    {
        /// <summary>
        /// Absolute path to this working directory on the local system.
        /// </summary>
        private string path;

        /// <summary>
        /// Initializes a new instance of the WorkingDirectory class.
        /// </summary>
        /// <param name="ironroot">
        /// Absolute path to the "iron" directory on the local system.
        /// </param>
        public WorkingDirectory(string ironroot)
        {
            // REVIEW: Have "nutemp" hard-wired here, or passed in?
            this.path = Path.Combine(ironroot, "nutemp", Path.GetRandomFileName());
            Directory.CreateDirectory(this.path);
        }

        /// <summary>
        /// Gets the absolute path to the root of this working directory on the local system.
        /// </summary>
        public string Root
        {
            get { return this.path; }
        }

        /// <summary>
        /// Gets the absolute path to the given build object in this working directory.
        /// </summary>
        /// <param name="obj">A build object.</param>
        /// <returns>The absolute path to the build object.</returns>
        public string PathTo(BuildObject obj)
        {
            return Path.Combine(this.path, obj.getRelativePath());
        }

        /// <summary>
        /// Gets the absolute path corresponding to the given relative path in this working directory.
        /// </summary>
        /// <param name="relativePath">Relative path to convert.</param>
        /// <returns>The absolute path corresponding to the given relative path.</returns>
        public string PathTo(string relativePath)
        {
            return Path.Combine(this.path, relativePath);
        }

        /// <summary>
        /// Creates the directory in the local filesystem that corresponds
        /// to this instance.
        /// </summary>
        /// <param name="obj">A build object.</param>
        public void CreateDirectoryFor(BuildObject obj)
        {
            Directory.CreateDirectory(Path.Combine(this.path, obj.getDirPath()));
        }

        /// <summary>
        /// Gets a collection of the build objects in this directory.
        /// </summary>
        /// <remarks>
        /// REVIEW: Return a collection of BuildObjectValuePointers instead?
        /// </remarks>
        /// <returns>A collection of build objects.</returns>
        public IEnumerable<BuildObject> GetContents()
        {
            List<BuildObject> contents = new List<BuildObject>();

            foreach (string fileName in Directory.EnumerateFiles(this.path))
            {
                contents.Add(new BuildObject(fileName));
            }

            return contents;
        }
    }
}
