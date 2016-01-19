//--
// <copyright file="ServiceConfiguration.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace AzureManager
{
    using System;
    using System.Diagnostics;
    using System.Globalization;
    using System.IO;
    using System.Text;
    using System.Xml;

    /// <summary>
    /// <para>
    /// Representation of the "service configuration" (.cscfg) file contents
    /// used for Azure deployments.
    /// </para>
    /// </summary>
    /// <remarks>
    /// <para>
    /// Format is defined by the "Azure Service Configuration Schema".
    /// See <see cref="https://msdn.microsoft.com/library/ee758710.aspx"/>.
    /// This class implements only the small subset of the schema that we use.
    /// </para>
    /// <para>
    /// This is the format of the "Configuration" member of various
    /// deployment-related classes (DeploymentChangeConfigurationParameters,
    /// DeploymentCreateParameters, DeploymentUpgradeParameters,
    /// HostedServiceGetDetailedResponse.Deployment, etc).
    /// </para>
    /// <para>
    /// Note that this is separate from the "Azure Service Definition Schema"
    /// (.csdef file) used to create the service proper.
    /// </para>
    /// </remarks>
    public class ServiceConfiguration
    {
        /// <summary>
        /// XML namespace for this object.
        /// </summary>
        public const string XmlNamespace = "http://schemas.microsoft.com/ServiceHosting/2008/10/ServiceConfiguration";

        /// <summary>
        /// XML element name for this object.
        /// </summary>
        public const string XmlTag = "ServiceConfiguration";

        /// <summary>
        /// XML attribute name for our service name field.
        /// </summary>
        private const string XmlServiceNameAttribute = "serviceName";

        /// <summary>
        /// XML attribute name for our OS family field.
        /// </summary>
        private const string XmlOSFamilyAttribute = "osFamily";

        /// <summary>
        /// XML attribute name for our OS version field.
        /// </summary>
        private const string XmlOSVersionAttribute = "osVersion";

        /// <summary>
        /// XML attribute name for our schema version field.
        /// </summary>
        private const string XmlSchemaVersionAttribute = "schemaVersion";

        /// <summary>
        /// XML element name for our role field.
        /// </summary>
        private const string XmlRoleElement = "Role";

        /// <summary>
        /// XML attribute name for our role name field.
        /// </summary>
        private const string XmlRoleNameAttribute = "name";

        // Note we don't currently support the "vmName" attribute.

        /// <summary>
        /// XML element name for our instances field.
        /// </summary>
        private const string XmlInstancesElement = "Instances";

        /// <summary>
        /// XML element name for our instance count field.
        /// </summary>
        private const string XmlInstanceCountAttribute = "count";

        /// <summary>
        /// XML element name for our configuration settings field.
        /// </summary>
        /// <remarks>
        /// Note we don't currently support any configuration settings.
        /// </remarks>
        private const string XmlConfigurationSettingsElement = "ConfigurationSettings";

        // Note we don't currently support any certificates.

        // Note we don't currently support the NetworkConfiguration element.

        /// <summary>
        /// Name of the service.
        /// </summary>
        private string serviceName;

        /// <summary>
        /// OS Family.
        /// </summary>
        private string osFamily;

        /// <summary>
        /// OS Version.
        /// </summary>
        private string osVersion;

        /// <summary>
        /// Schema Version.
        /// </summary>
        private string schemaVersion;

        /// <summary>
        /// Name of the role.
        /// </summary>
        private string roleName;

        /// <summary>
        /// Count of the number of role instances.
        /// </summary>
        private int instanceCount;

        /// <summary>
        /// Initializes a new instance of the ServiceConfiguration class.
        /// </summary>
        /// <param name="serviceName">Name of the cloud service.</param>
        /// <param name="osFamily">Guest OS that will run on role instances in the cloud service.</param>
        /// <param name="osVersion">Version of the Guest OS that will run on role instances in the cloud service.</param>
        /// <param name="schemaVersion">Version of the Service Configuration schema.</param>
        /// <param name="roleName">Name of the role.</param>
        /// <param name="instanceCount">Number of instances to deploy for this role.</param>
        public ServiceConfiguration(
            string serviceName,
            string osFamily,
            string osVersion,
            string schemaVersion,
            string roleName,
            int instanceCount)
        {
            this.serviceName = serviceName;
            this.osFamily = osFamily;
            this.osVersion = osVersion;
            this.schemaVersion = schemaVersion;
            this.roleName = roleName;
            this.instanceCount = instanceCount;
        }

        /// <summary>
        /// Gets the service name.
        /// </summary>
        public string ServiceName
        {
            get { return this.serviceName; }
        }

        /// <summary>
        /// Gets the OS Family.
        /// </summary>
        public string OsFamily
        {
            get { return this.osFamily; }
        }

        /// <summary>
        /// Gets the OS Version.
        /// </summary>
        public string OsVersion
        {
            get { return this.osVersion; }
        }

        /// <summary>
        /// Gets the Schema Version.
        /// </summary>
        public string SchemaVersion
        {
            get { return this.schemaVersion; }
        }

        /// <summary>
        /// Gets the name of the role.
        /// </summary>
        public string RoleName
        {
            get { return this.roleName; }
        }

        /// <summary>
        /// Gets the number of instances.
        /// </summary>
        public int InstanceCount
        {
            get { return this.instanceCount; }
        }

        /// <summary>
        /// Creates a ServiceConfiguration from an XML representation.
        /// </summary>
        /// <param name="xs">
        /// A string containing an XML document representing a request.
        /// </param>
        /// <returns>
        /// A new request corresponding to the XML representation read.
        /// </returns>
        public static ServiceConfiguration FromXml(string xs)
        {
            XmlReader xr = XmlReader.Create(new StringReader(xs));
            while (xr.Read())
            {
                if (xr.NodeType == XmlNodeType.Element)
                {
                    break;
                }
            }

            return ReadXml(xr);
        }

        /// <summary>
        /// Helper function to read an XML element (not a full document)
        /// representing an Azure Service Configuration.
        /// </summary>
        /// <remarks>
        /// Note that the XmlReader is expected to be positioned in the XML
        /// document such that the current node is a request element.
        /// </remarks>
        /// <param name="xr">The XmlReader object to read from.</param>
        /// <returns>
        /// A new request corresponding to the XML representation read.
        /// </returns>
        public static ServiceConfiguration ReadXml(XmlReader xr)
        {
            Debug.Assert(xr.Name.Equals(ServiceConfiguration.XmlTag), "Invalid call");

            string serviceName = xr.GetAttribute(ServiceConfiguration.XmlServiceNameAttribute);
            string osFamily = xr.GetAttribute(ServiceConfiguration.XmlOSFamilyAttribute);
            string osVersion = xr.GetAttribute(ServiceConfiguration.XmlOSVersionAttribute);
            string schemaVersion = xr.GetAttribute(ServiceConfiguration.XmlSchemaVersionAttribute);

            string roleName = string.Empty;
            int instanceCount = 0;

            while (xr.Read())
            {
                if (xr.NodeType == XmlNodeType.Element)
                {
                    switch (xr.Name)
                    {
                        case XmlRoleElement:
                            roleName = xr.GetAttribute(ServiceConfiguration.XmlRoleNameAttribute);
                            break;

                        case XmlInstancesElement:
                            string temp = xr.GetAttribute(ServiceConfiguration.XmlInstanceCountAttribute);
                            instanceCount = int.Parse(temp);
                            break;

                        case XmlConfigurationSettingsElement:
                            break;
                    }
                }
                else if (xr.NodeType == XmlNodeType.EndElement)
                {
                    if (xr.Name.Equals(ServiceConfiguration.XmlTag))
                    {
                        break;  // All done.
                    }
                }
            }

            // REVIEW: Sanity check elements here?
            return new ServiceConfiguration(
                serviceName,
                osFamily,
                osVersion,
                schemaVersion,
                roleName,
                instanceCount);
        }

        /// <summary>
        /// Creates an XML document representing this cloud execution request.
        /// </summary>
        /// <returns>
        /// A string containing an XML document representing this request.
        /// </returns>
        public string ToXml()
        {
            StringBuilder sb = new StringBuilder();
            XmlWriterSettings settings = new XmlWriterSettings();
            settings.Indent = true;
            ////settings.OmitXmlDeclaration = true;
            XmlWriter xw = XmlWriter.Create(sb, settings);
            xw.WriteStartDocument();
            this.WriteXml(xw);
            xw.Close();
            return sb.ToString();
        }

        /// <summary>
        /// Helper function to write an XML element (not a full document)
        /// representing this result record.
        /// </summary>
        /// <param name="xw">The XmlWriter object to write to.</param>
        public void WriteXml(XmlWriter xw)
        {
            // Start writing the element for this object.
            xw.WriteStartElement(XmlTag, ServiceConfiguration.XmlNamespace);
            xw.WriteAttributeString(ServiceConfiguration.XmlServiceNameAttribute, this.serviceName);
            xw.WriteAttributeString(ServiceConfiguration.XmlOSFamilyAttribute, this.osFamily);
            xw.WriteAttributeString(ServiceConfiguration.XmlOSVersionAttribute, this.osVersion);
            xw.WriteAttributeString(ServiceConfiguration.XmlSchemaVersionAttribute, this.schemaVersion);

            // Start writing the Role element.
            xw.WriteStartElement(ServiceConfiguration.XmlRoleElement);
            xw.WriteAttributeString(ServiceConfiguration.XmlRoleNameAttribute, this.roleName);

            // Write the Instances element.
            xw.WriteStartElement(ServiceConfiguration.XmlInstancesElement);
            xw.WriteAttributeString(ServiceConfiguration.XmlInstanceCountAttribute, this.instanceCount.ToString(CultureInfo.InvariantCulture));
            xw.WriteEndElement();

            // Write the ConfigurationSettings element.
            xw.WriteElementString(ServiceConfiguration.XmlConfigurationSettingsElement, string.Empty);

            // Finish writing the Role element.
            xw.WriteEndElement();

            // Finish writing the element for this object.
            xw.WriteEndElement();
        }

        /// <summary>
        /// Gets a string representation of this instance.
        /// Primarily intended as a debugging aid.
        /// </summary>
        /// <returns>A string representation of this instance.</returns>
        public override string ToString()
        {
            StringBuilder output = new StringBuilder();

            output.AppendFormat("Service Name: {0}", this.serviceName);
            output.AppendLine();
            output.AppendFormat("OS Family: {0}", this.osFamily);
            output.AppendLine();
            output.AppendFormat("OS Version: {0}", this.osVersion);
            output.AppendLine();
            output.AppendFormat("Schema Version: {0}", this.schemaVersion);
            output.AppendLine();
            output.AppendFormat("Role Name: {0}", this.roleName);
            output.AppendLine();
            output.AppendFormat("Number of Instances: {0}", this.instanceCount);
            output.AppendLine();

            return output.ToString();
        }
    }
}
