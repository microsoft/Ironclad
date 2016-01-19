//--
// <copyright file="XmlFiller.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Xml;

    /// <summary>
    /// REVIEW: Does this need to be an interface?
    /// TODO: Rename to IXmlFiller if we need to keep this.
    /// </summary>
    internal interface XmlFiller
    {
        void fillXml(XmlWriter xml);
    }
}
