//--
// <copyright file="BuildObject.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Diagnostics;
    using System.IO;
    using System.Linq;
    using System.Xml;

    /// <summary>
    /// An abstract identifier for "nouns" (i.e. the things that verbs operate
    /// on -- both verb outputs and dependencies are BuildObjects).
    /// </summary>
    /// <remarks>
    /// Note that sometimes the code and/or comments about the code refer to
    /// BuildObjects as if they are the concrete thing that they identify as
    /// opposed to just being the abstract identifier for that thing.  This is
    /// probably okay, as there should be just one concrete instance of any
    /// particular abstract build object during a given run of the system.
    /// </remarks>
    public class BuildObject
    {
        /// <summary>
        /// The XML element name for this object.
        /// </summary>
        public const string XmlTag = "BuildObject";

        /// <summary>
        /// Path to this object as stored in the local filesystem, relative to
        /// the IronRoot (i.e. begins with "src", "obj", etc.).
        /// </summary>
        /// <remarks>
        /// This string is expected to be normalized to have consistent casing.
        /// </remarks>
        protected string path;

        /// <summary>
        /// Whether this object is considered "trusted" for verification
        /// purposes.
        /// </summary>
        private bool isTrusted;

        /// <summary>
        /// The filename of this object, without the file extension.
        /// </summary>
        private string filenameWithoutExtension;

        /// <summary>
        /// The filename extension for this object.
        /// </summary>
        private string filenameExtension;

        /// <summary>
        /// Initializes a new instance of the BuildObject class.
        /// </summary>
        /// <param name="path">
        /// Relative path to this object in the local filesystem.
        /// </param>
        /// <param name="isTrusted">
        /// Whether this object is considered "trusted" for verification
        /// purposes.
        /// </param>
        public BuildObject(string path, bool isTrusted = false)
        {
            // ToDo: Fix VSSolutionVerb and/or IronfleetTestDriver.sln to work in "src" tree without hitting below Assert.  Then re-instate below Assert.
            ////Util.Assert(!path.StartsWith(BuildEngine.theEngine.getSrcRoot(), StringComparison.OrdinalIgnoreCase));
            this.path = BuildEngine.theEngine.normalizeIronPath(path);
            this.isTrusted = isTrusted;
        }

        /// <summary>
        /// Initializes a new instance of the BuildObject class.
        /// </summary>
        /// <param name="path">
        /// Relative path to this object in the local filesystem.
        /// </param>
        protected BuildObject(string path)
        {
            this.path = BuildEngine.theEngine.normalizeIronPath(path);
        }

        /// <summary>
        /// Gets or sets a value indicating whether this object is considered
        /// "trusted" for verification purposes.
        /// </summary>
        /// <remarks>
        /// REVIEW: Giving build objects properties like this is dangerous,
        /// as they are supposed to be just abstract ids.  Two equivalent
        /// (per Equals() below) build objects could be created, and should
        /// reference the same bag of bits, yet have different properties!
        /// </remarks>
        public bool IsTrusted
        {
            get { return this.isTrusted; }
            protected set { this.isTrusted = value; }
        }

        /// <summary>
        /// Gets the relative path for this instance.
        /// </summary>
        /// <remarks>
        /// TODO: Replace this with a property ("RelativePath"?) that is
        /// public get and protected set.  And change this.path from
        /// protected to private.
        /// </remarks>
        /// <returns>The relative path for this instance.</returns>
        public string getRelativePath()
        {
            return this.path;
        }

        /// <summary>
        /// Returns a string that represents this instance.
        /// </summary>
        /// <returns>A string that represents this instance.</returns>
        public override string ToString()
        {
            return this.path;
        }

        /// <summary>
        /// Gets the directory information for this instance.
        /// </summary>
        /// <returns>The directory information for this instance.</returns>
        public string getDirPath()
        {
            return Path.GetDirectoryName(this.path);
        }

        /// <summary>
        /// Gets the file name and extension for this instance.
        /// </summary>
        /// <returns>The file name and extension for this instance.</returns>
        public string getFileName()
        {
            return Path.GetFileName(this.path);
        }

        /// <summary>
        /// Gets the file name (sans extension) for this instance.
        /// </summary>
        /// <returns>The file name (sans extension) for this instance.</returns>
        public string getFileNameWithoutExtension()
        {
            this.splitExtension();
            return this.filenameWithoutExtension;
        }

        /// <summary>
        /// Gets the file extension for this instance.
        /// </summary>
        /// <returns>The file extension for this instance.</returns>
        public string getExtension()
        {
            this.splitExtension();
            return this.filenameExtension;
        }

        /// <summary>
        /// Determines whether this instance and another specified BuildObject
        /// object have the same value (identity?).  Really, the same path.
        /// </summary>
        /// <param name="obj">The object to compare to this instance.</param>
        /// <returns>
        /// True if the given object is equivalent to this instance,
        /// false otherwise.
        /// </returns>
        public override bool Equals(object obj)
        {
            BuildObject other = obj as BuildObject;
            if (other != null)
            {
                return this.path.Equals(other.path, StringComparison.Ordinal);
            }
            else
            {
                return false;
            }
        }

        /// <summary>
        /// Returns the hash code for this instance.
        /// </summary>
        /// <remarks>
        /// Note that equivalent (as in .Equals returns true) instances
        /// will have the same hash code.
        /// </remarks>
        /// <returns>The hash code for this instance.</returns>
        public override int GetHashCode()
        {
            return this.path.GetHashCode();
        }

        /// <summary>
        /// Creates a new instance based on this one, but with the given
        /// extension, and guaranteed to be in the obj directory.
        /// </summary>
        /// <param name="extension">Extension to give new instance.</param>
        /// <returns>A new instance.</returns>
        public BuildObject makeOutputObject(string extension)
        {
            return new BuildObject(this.mashedPathname(BuildEngine.theEngine.getObjRoot(), extension));
        }

        /// <summary>
        /// Creates a new instance based on this one, but for the given
        /// appLabel (REVIEW: what does this mean?), with the given
        /// extension, and guaranteed to be in the obj directory.
        /// </summary>
        /// <param name="appLabel">The app label to use.</param>
        /// <param name="extension">Extension to give new instance.</param>
        /// <returns>A new instance.</returns>
        public BuildObject makeLabeledOutputObject(string appLabel, string extension)
        {
            string appSpecificPrefix =
                appLabel == null
                ? BuildEngine.theEngine.getObjRoot()
                : Path.Combine(BuildEngine.theEngine.getObjRoot(), appLabel);

            // REVIEW: Ordinal vs. OrdinalIgnoreCase.
            if (this.path.StartsWith(appSpecificPrefix, StringComparison.OrdinalIgnoreCase))
            {
                // Input is already in the correct subtree; don't nest subtrees.
                return this.makeOutputObject(extension);
            }
            else
            {
                // Input is coming from elsewhere; give it a parallel location under app-specific subtree.
                return new BuildObject(this.mashedPathname(appSpecificPrefix, extension));
            }
        }

        /// <summary>
        /// Creates a new VirtualBuildObject based on this instance, but with
        /// a path modified to be virtual and have the given extension.
        /// </summary>
        /// <param name="extension">
        /// Filename extension to give the new object.
        /// </param>
        /// <returns>A new VirtualBuildObject.</returns>
        public BuildObject makeVirtualObject(string extension)
        {
            return new VirtualBuildObject(this.mashedPathname(BuildEngine.theEngine.getVirtualRoot(), extension));
        }

        /// <summary>
        /// Helper function to read an XML element (not a full document)
        /// representing a BuildObject.
        /// </summary>
        /// <remarks>
        /// Note that the XmlReader is expected to be positioned in the XML
        /// document such that the current node is a BuildObject element.
        /// </remarks>
        /// <param name="xr">The XmlReader object to read from.</param>
        /// <returns>
        /// A new BuildObject corresponding to the XML representation read.
        /// </returns>
        public static BuildObject ReadXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(XmlTag));
            string relativePath = xr.ReadElementContentAsString();
            return new BuildObject(relativePath);
        }

        /// <summary>
        /// Helper function to write an XML element (not a full document)
        /// representing this BuildObject.
        /// </summary>
        /// <param name="xw">The XmlWriter object to write to.</param>
        public void WriteXml(XmlWriter xw)
        {
            xw.WriteStartElement(XmlTag);
            xw.WriteString(this.path);
            xw.WriteEndElement();
        }

        /// <summary>
        /// Splits the filename of this object into its separate base and
        /// extension components.
        /// </summary>
        private void splitExtension()
        {
            if (this.filenameWithoutExtension == null)
            {
                string filename = this.getFileName();
                int dot = filename.IndexOf('.');
                if (dot < 0)
                {
                    this.filenameWithoutExtension = filename;
                    this.filenameExtension = null;
                }
                else
                {
                    this.filenameExtension = filename.Substring(dot);

                    // TODO: This is a (possibly brittle) workaround for dfy .s
                    // and .i, which aren't part of the file type, they're part
                    // of the name. Sorta.
                    if (DafnyTransformBaseVerb.DAFNY_LONG_EXTNS.Contains(this.filenameExtension))
                    {
                        dot += 2;
                        this.filenameExtension = filename.Substring(dot);
                    }

                    this.filenameWithoutExtension = filename.Substring(0, dot);
                }
            }
        }

        /// <summary>
        /// Combines the provided root path and extension with this
        /// instance's relative path and munged (for DafnySpec/CC) filename.
        /// </summary>
        /// <param name="root">The desired root path.</param>
        /// <param name="extension">The desired extension.</param>
        /// <returns>A combined pathname.</returns>
        private string mashedPathname(string root, string extension)
        {
            string filename = this.getFileNameWithoutExtension();

            // Remap dafny filenames so resulting objects have correctly-parsed extns.
            filename = Util.dafnySpecMungeName(filename);

            return Path.Combine(root, this.getDirRelativeToSrcOrObj(), filename + extension);
        }

        /// <summary>
        /// Strips off the initial 'src\' or 'obj\' from the path.
        /// </summary>
        /// <returns>
        /// The directory containing this object, relative to the source or
        /// object directory.
        /// </returns>
        private string getDirRelativeToSrcOrObj()
        {
            string dirname = this.getDirPath();
            int slash = dirname.IndexOf('\\');
            Util.Assert(slash >= 0);
            return dirname.Substring(slash + 1);
        }
    }
}
