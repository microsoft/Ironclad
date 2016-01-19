//--
// <copyright file="CloudExecutionRequest.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Globalization;
    using System.IO;
    using System.Text;
    using System.Xml;
    using Microsoft.WindowsAzure.Storage.Queue;

    /// <summary>
    /// Message that is put on the cloud "requests" queue to ask a cloud
    /// execution engine to do some work on the requester's behalf.
    /// </summary>
    public class CloudExecutionRequest
    {
        /// <summary>
        /// XML element name for this object.
        /// </summary>
        public const string XmlTag = "CloudExecutionRequest";

        /// <summary>
        /// Version of this object we create by default.
        /// </summary>
        private const int Version = 2;

        /// <summary>
        /// XML element name for our version field.
        /// </summary>
        private const string XmlVersionAttribute = "Version";

        /// <summary>
        /// XML element name for our reportQueue field.
        /// </summary>
        private const string XmlReportQueueElement = "ReportQueue";

        /// <summary>
        /// XML element name for our identifier field.
        /// </summary>
        private const string XmlIdentifierElement = "Identifier";

        /// <summary>
        /// XML element name for our operation field.
        /// </summary>
        private const string XmlOperationElement = "Operation";

        /// <summary>
        /// XML element name for our executable field.
        /// </summary>
        private const string XmlExecutableElement = "Executable";

        /// <summary>
        /// XML element name for our arguments field.
        /// </summary>
        private const string XmlArgumentsElement = "Arguments";

        /// <summary>
        /// XML element name for our inputFileMappings field.
        /// </summary>
        private const string XmlInputFileMappingsElement = "InputFileMappings";

        /// <summary>
        /// XML element name for our outputFiles field.
        /// </summary>
        private const string XmlOutputFilesElement = "OutputFiles";

        /// <summary>
        /// Queued message this instance was created from (if it was).
        /// </summary>
        private CloudQueueMessage message;

        /// <summary>
        /// Version of this object instance.
        /// </summary>
        private int version;

        /// <summary>
        /// Queue on which to add the report of the disposition of this request.
        /// </summary>
        private string reportQueue;

        /// <summary>
        /// Unique identifier for this request.
        /// </summary>
        private string identifier;

        /// <summary>
        /// Operation to perform.
        /// </summary>
        private Operation operation;

        /// <summary>
        /// Executable to be run.
        /// </summary>
        private string executable;

        /// <summary>
        /// Arguments to the executable.
        /// </summary>
        private string arguments;

        /// <summary>
        /// Collection of input files required for this execution,
        /// represented by both their item cache identifier and
        /// their relative path.
        /// </summary>
        private List<BuildObjectValuePointer> inputFileMappings;

        /// <summary>
        /// Collection of expected output files from this execution.
        /// </summary>
        private IEnumerable<BuildObject> outputFiles;

        /// <summary>
        /// Initializes a new instance of the CloudExecutionRequest class.
        /// </summary>
        /// <param name="reportQueue">
        /// Queue on which to add the report of the disposition of this request.
        /// </param>
        /// <param name="identifier">Unique ID for this instance.</param>
        /// <param name="operation">Operation to perform.</param>
        /// <param name="executable">Executable to be run.</param>
        /// <param name="arguments">Arguments to the executable.</param>
        /// <param name="inputFileMappings">
        /// Input files required for this execution.
        /// </param>
        /// <param name="outputFiles">Expected output files.</param>
        public CloudExecutionRequest(
            string reportQueue,
            string identifier,
            Operation operation,
            string executable,
            string arguments,
            List<BuildObjectValuePointer> inputFileMappings,
            IEnumerable<BuildObject> outputFiles)
            : this(
                CloudExecutionRequest.Version,
                reportQueue,
                identifier,
                operation,
                executable,
                arguments,
                inputFileMappings,
                outputFiles)
        {
            // REVIEW: Use different random string generator for identifier?
        }

        /// <summary>
        /// Initializes a new instance of the CloudExecutionRequest class.
        /// </summary>
        /// <param name="version">Version of this class instance.</param>
        /// <param name="reportQueue">
        /// Queue on which to add the report of the disposition of this request.
        /// </param>
        /// <param name="identifier">Unique ID for this instance.</param>
        /// <param name="operation">Operation to perform.</param>
        /// <param name="executable">Executable to be run.</param>
        /// <param name="arguments">Arguments to the executable.</param>
        /// <param name="inputFileMappings">
        /// Input files required for this execution.
        /// </param>
        /// <param name="outputFiles">Expected output files.</param>
        private CloudExecutionRequest(
            int version,
            string reportQueue,
            string identifier,
            Operation operation,
            string executable,
            string arguments,
            List<BuildObjectValuePointer> inputFileMappings,
            IEnumerable<BuildObject> outputFiles)
        {
            this.version = version;
            this.reportQueue = reportQueue;
            this.identifier = identifier;
            this.operation = operation;
            this.executable = executable;
            this.arguments = arguments;
            this.inputFileMappings = inputFileMappings;
            this.outputFiles = outputFiles;
        }

        /// <summary>
        /// Various types of operation that can be requested.
        /// </summary>
        public enum Operation : int
        {
            /// <summary>
            /// Don't do anything (no-op).
            /// </summary>
            None,

            /// <summary>
            /// Run the specified executable.
            /// </summary>
            RunExecutable,

            /// <summary>
            /// Delete the specified report queue.
            /// </summary>
            DeleteQueue,

            /// <summary>
            /// Exit (and thus quit handling requests).
            /// </summary>
            CommitSuicide,
        }

        /// <summary>
        /// Gets the CloudQueueMessage this instance was derived from (if any).
        /// </summary>
        public CloudQueueMessage Message
        {
            get { return this.message; }
        }

        /// <summary>
        /// Gets the queue on which to report the disposition of this request.
        /// </summary>
        public string ReportQueue
        {
            get { return this.reportQueue; }
        }

        /// <summary>
        /// Gets the unique identifier for this request.
        /// </summary>
        public string Identifier
        {
            get { return this.identifier; }
        }

        /// <summary>
        /// Gets the operation to perform.
        /// </summary>
        public Operation RequestedOperation
        {
            get { return this.operation; }
        }

        /// <summary>
        /// Gets the executable to run.
        /// </summary>
        public string Executable
        {
            get { return this.executable; }
        }

        /// <summary>
        /// Gets the arguments to the executable.
        /// </summary>
        public string Arguments
        {
            get { return this.arguments; }
        }

        /// <summary>
        /// Gets the collection of files needed as input to the execution,
        /// as both BuildObjects and as their cached hash values.
        /// </summary>
        public IEnumerable<BuildObjectValuePointer> InputFileMappings
        {
            get { return this.inputFileMappings; }
        }

        /// <summary>
        /// Gets the collection of potential output files from this execution,
        /// as BuildObjects.
        /// </summary>
        public IEnumerable<BuildObject> OutputFiles
        {
            get { return this.outputFiles; }
        }

        /// <summary>
        /// Creates a CloudExecutionRequest from a CloudQueueMessage
        /// representation.
        /// </summary>
        /// <param name="message">
        /// A CloudQueueMessage containing an XML document representing a
        /// CloudExecutionRequest.
        /// </param>
        /// <returns>
        /// A new request corresponding to the XML representation contained in
        /// the message.
        /// </returns>
        public static CloudExecutionRequest FromMessage(CloudQueueMessage message)
        {
            CloudExecutionRequest request = CloudExecutionRequest.FromXml(message.AsString);
            request.message = message;

            return request;
        }

        /// <summary>
        /// Creates a CloudExecutionRequest from an XML representation.
        /// </summary>
        /// <param name="xs">
        /// A string containing an XML document representing a request.
        /// </param>
        /// <returns>
        /// A new request corresponding to the XML representation read.
        /// </returns>
        public static CloudExecutionRequest FromXml(string xs)
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
        /// representing a cloud execution request.
        /// </summary>
        /// <remarks>
        /// Note that the XmlReader is expected to be positioned in the XML
        /// document such that the current node is a request element.
        /// </remarks>
        /// <param name="xr">The XmlReader object to read from.</param>
        /// <returns>
        /// A new request corresponding to the XML representation read.
        /// </returns>
        public static CloudExecutionRequest ReadXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(CloudExecutionRequest.XmlTag));

            string versionText = xr.GetAttribute(CloudExecutionRequest.XmlVersionAttribute);
            int version = int.Parse(versionText, CultureInfo.InvariantCulture);

            string reportQueue = "reports";
            string identifier = string.Empty;
            Operation operation = Operation.RunExecutable;
            string executable = string.Empty;
            string arguments = string.Empty;
            bool inInputFileMappings = false;
            List<BuildObjectValuePointer> inputFileMappings = new List<BuildObjectValuePointer>();
            bool inOutputFiles = false;
            List<BuildObject> outputFiles = new List<BuildObject>();
            while (xr.Read())
            {
                if (xr.NodeType == XmlNodeType.Element)
                {
                    switch (xr.Name)
                    {
                        case XmlReportQueueElement:
                            reportQueue = xr.ReadElementContentAsString();
                            break;

                        case XmlIdentifierElement:
                            identifier = xr.ReadElementContentAsString();
                            break;

                        case XmlOperationElement:
                            operation = (Operation)Enum.Parse(typeof(Operation), xr.ReadElementContentAsString());
                            break;

                        case XmlExecutableElement:
                            executable = xr.ReadElementContentAsString();
                            break;

                        case XmlArgumentsElement:
                            arguments = xr.ReadElementContentAsString();
                            break;

                        case XmlInputFileMappingsElement:
                            inInputFileMappings = true;
                            break;

                        case BuildObjectValuePointer.XmlTag:
                            Util.Assert(inInputFileMappings);
                            inputFileMappings.Add(BuildObjectValuePointer.ReadXml(xr));
                            break;

                        case XmlOutputFilesElement:
                            inOutputFiles = true;
                            break;

                        case BuildObject.XmlTag:
                            Util.Assert(inOutputFiles);
                            outputFiles.Add(BuildObject.ReadXml(xr));
                            break;
                    }
                }
                else if (xr.NodeType == XmlNodeType.EndElement)
                {
                    if (xr.Name.Equals(CloudExecutionRequest.XmlTag))
                    {
                        break;  // All done.
                    }

                    switch (xr.Name)
                    {
                        case XmlInputFileMappingsElement:
                            inInputFileMappings = false;
                            break;

                        case XmlOutputFilesElement:
                            inOutputFiles = false;
                            break;
                    }
                }
            }

            // REVIEW: Require presence of (some/all) elements?  Sanity check things here?
            return new CloudExecutionRequest(
                version,
                reportQueue,
                identifier,
                operation,
                executable,
                arguments,
                inputFileMappings,
                outputFiles);
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
            xw.WriteStartElement(XmlTag);
            xw.WriteAttributeString(CloudExecutionRequest.XmlVersionAttribute, this.version.ToString(CultureInfo.InvariantCulture));

            // Write the ReportQueue element.
            xw.WriteElementString(XmlReportQueueElement, this.reportQueue);

            // Optionally write the Identifier element.
            if (!string.IsNullOrEmpty(this.identifier))
            {
                xw.WriteElementString(CloudExecutionRequest.XmlIdentifierElement, this.identifier);
            }

            // Write the Operation element.
            xw.WriteElementString(XmlOperationElement, this.operation.ToString());

            if (this.operation == Operation.RunExecutable)
            {
                // Write the Executable element.
                xw.WriteElementString(XmlExecutableElement, this.executable);

                // Write the Arguments element.
                xw.WriteElementString(XmlArgumentsElement, this.arguments);

                // Write the InputFileMappings element.
                xw.WriteStartElement(XmlInputFileMappingsElement);
                foreach (BuildObjectValuePointer inputFile in this.inputFileMappings)
                {
                    inputFile.WriteXml(xw);
                }

                xw.WriteEndElement();

                // Write the OutputFiles element.
                xw.WriteStartElement(XmlOutputFilesElement);
                foreach (BuildObject outputFile in this.outputFiles)
                {
                    outputFile.WriteXml(xw);
                }

                xw.WriteEndElement();
            }

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

            output.AppendFormat("Version: {0}", this.version);
            output.AppendLine();
            output.AppendFormat("Report Queue: {0}", this.reportQueue);
            output.AppendLine();
            output.AppendFormat("Identifier: {0}", this.identifier);
            output.AppendLine();
            output.AppendFormat("Operation: {0}", this.operation);
            output.AppendLine();
            output.AppendFormat("Executable: {0}", this.executable);
            output.AppendLine();
            output.AppendFormat("Arguments: {0}", this.arguments);
            output.AppendLine();

            output.AppendFormat("InputFileMappings ({0} files):", this.inputFileMappings.Count);
            output.AppendLine();
#if false
            foreach (BuildObjectValuePointer mapping in this.inputFileMappings)
            {
                output.AppendFormat("{0} = {1}", mapping.RelativePath, mapping.ObjectHash);
                output.AppendLine();
            }
#endif

            output.AppendLine("OutputFiles:");
            foreach (BuildObject file in this.outputFiles)
            {
                output.AppendLine(file.getRelativePath());
            }

            return output.ToString();
        }
    }
}
