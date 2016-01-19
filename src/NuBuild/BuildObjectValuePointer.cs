//--
// <copyright file="BuildObjectValuePointer.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Xml;

    /// <summary>
    /// Mapping between a BuildObject (an abstract identifier) and the hash
    /// value of the build object's contents (concrete identifier) for this run.
    /// REVIEW: Come up with a better name for this?
    /// </summary>
    public class BuildObjectValuePointer
    {
        /// <summary>
        /// The XML element name for this object.
        /// </summary>
        public const string XmlTag = "BuildObjectValuePointer";

        /// <summary>
        /// The XML attribute name for the ObjectHash value.
        /// </summary>
        private const string XmlObjectHashAttribute = "ObjectHash";

        /// <summary>
        /// The XML attribute name for the RelativePath value.
        /// </summary>
        private const string XmlRelativePathAttribute = "RelativePath";

        /// <summary>
        /// Hash of the contents referenced by the build object.
        /// </summary>
        private string objectHash;

        /// <summary>
        /// Path to the build object, relative to the IronRoot.
        /// </summary>
        private string relativePath;

        /// <summary>
        /// Initializes a new instance of the BuildObjectValuePointer class.
        /// </summary>
        /// <param name="objectHash">
        /// Hash of the contents referenced by the build object.
        /// </param>
        /// <param name="relativePath">
        /// Path to the build object, relative to the IronRoot.
        /// </param>
        public BuildObjectValuePointer(string objectHash, string relativePath)
        {
            this.objectHash = objectHash;
            this.relativePath = relativePath;
        }

        /// <summary>
        /// Gets the hash of the contents referenced by the build object.
        /// </summary>
        public string ObjectHash
        {
            get { return this.objectHash; }
        }

        /// <summary>
        /// Gets the path to the build object, relative to the IronRoot.
        /// </summary>
        public string RelativePath
        {
            get { return this.relativePath; } 
        }

        /// <summary>
        /// Helper function to read an XML element (not a full document)
        /// representing a BuildObjectValuePointer.
        /// </summary>
        /// <remarks>
        /// Note that the XmlReader is expected to be positioned in the XML
        /// document such that the current node is a BuildObjectValuePointer
        /// element.
        /// </remarks>
        /// <param name="xr">The XmlReader object to read from.</param>
        /// <returns>
        /// A new BuildObjectValuePointer corresponding to the XML
        /// representation read.
        /// </returns>
        public static BuildObjectValuePointer ReadXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(XmlTag));
            string objectHash = xr.GetAttribute(XmlObjectHashAttribute);
            string relativePath = xr.GetAttribute(XmlRelativePathAttribute);
            return new BuildObjectValuePointer(objectHash, relativePath);
        }

        /// <summary>
        /// Helper function to write an XML element (not a full document)
        /// representing this BuildObjectValuePointer.
        /// </summary>
        /// <param name="xw">The XmlWriter object to write to.</param>
        public void WriteXml(XmlWriter xw)
        {
            xw.WriteStartElement(XmlTag);
            xw.WriteAttributeString(XmlObjectHashAttribute, this.objectHash);
            xw.WriteAttributeString(XmlRelativePathAttribute, this.relativePath);
            xw.WriteEndElement();
        }
    }
}
