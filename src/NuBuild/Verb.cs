//--
// <copyright file="Verb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Xml;

    internal abstract class Verb
        : IVerb
    {
        public override bool Equals(object obj)
        {
            IVerb other = obj as IVerb;
            if (other != null)
            {
                return this.getAbstractIdentifier().Equals(other.getAbstractIdentifier());
            }
            else
            {
                return false;
            }
        }

        public override int GetHashCode()
        {
            return this.getAbstractIdentifier().GetHashCode();
        }

        public override string ToString()
        {
            return this.getAbstractIdentifier().ToString();
        }

        public int CompareTo(object other)
        {
            return this.getAbstractIdentifier().CompareTo(((IVerb)other).getAbstractIdentifier());
        }

        public abstract IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp);

        public abstract IEnumerable<IVerb> getVerbs();

        public abstract IEnumerable<BuildObject> getOutputs();

        public virtual BuildObject getDiagnosticsBase()
        {
            return new BuildObject(Path.Combine(
                BuildEngine.theEngine.getObjRoot(), "diagnostics", Util.mungeClean(this.getAbstractIdentifier().ToString())));
        }

        public virtual IEnumerable<BuildObject> getFailureOutputs()
        {
            return new BuildObject[]
            {
                this.getDiagnosticsBase().makeOutputObject(".bat"),
                this.getDiagnosticsBase().makeOutputObject(".stdout"),
                this.getDiagnosticsBase().makeOutputObject(".stderr"),
            };
        }

        public abstract IVerbWorker getWorker(WorkingDirectory workingDirectory);

        // Called by tool when this is the top-level output, it has generated a Fresh
        // result, and we want to print that result on the display.
        public virtual Presentation getPresentation()
        {
            PresentationBuilder pr = new PresentationBuilder();
            pr.line("Okay.");
            return pr.fix();
        }

        // Called by tool when we want a short (one-line)
        // summary for showing in-progress results.
        public virtual Presentation getRealtimePresentation(Disposition d)
        {
            PresentationBuilder pr = new PresentationBuilder();
            pr.startLine();
            pr.color(
                d is Fresh ? Presentation.GREEN : Presentation.RED,
                this.ToString() + " " + d.ToString());
            pr.endLine();
            if (d is Failed)
            {
                // This isn't a verification failure, a tool itself broke.
                // Provide that report.
                foreach (string m in d.getMessages())
                {
                    pr.pre(Presentation.abbreviateLines(m));
                }
            }

            return pr.fix();
        }

        ////////////////////////////////////////////////////

        // Handy helper for verbs using ProcessInvoker.
        private bool cpuTimeSecondsValid = false;
        private double cpuTimeSeconds;

        public virtual void RecordProcessInvokeCpuTime(double cpuTimeSeconds)
        {
            this.cpuTimeSeconds = cpuTimeSeconds;
            this.cpuTimeSecondsValid = true;
        }

        public static string XML_SubprocessTiming = "SubprocessTiming";
        public static string XML_SubprocessTiming_Valid_Attr = "Valid";
        public static string XML_SubprocessTiming_CPUTimeSeconds_Attr = "CPUTimeSeconds";

        public void writeTimingXml(XmlWriter xw)
        {
            xw.WriteStartElement(XML_SubprocessTiming);
            xw.WriteAttributeString(XML_SubprocessTiming_Valid_Attr, this.cpuTimeSecondsValid.ToString());
            if (this.cpuTimeSecondsValid)
            {
                xw.WriteAttributeString(XML_SubprocessTiming_CPUTimeSeconds_Attr, this.cpuTimeSeconds.ToString());
            }

            xw.WriteEndElement();
        }

        ////////////////////////////////////////////////////

        public abstract AbstractId getAbstractIdentifier();

        public static string XML_DebugVerb = "DebugVerb";
        public static string XML_DebugVerb_Value_Attr = "value";

        public static string XML_DebugDep = "DebugDep";
        public static string XML_DebugDep_Name_Attr = "name";
        public static string XML_DebugDep_Hash_Attr = "hash";

        public void writeDebugXml(XmlWriter xw)
        {
            xw.WriteStartElement(XML_DebugVerb);
            xw.WriteAttributeString(XML_DebugVerb_Value_Attr, this.getAbstractIdentifier().ToString());
            xw.WriteEndElement();

            DependencyDisposition ddisp;
            foreach (BuildObject obj in this.getDependencies(out ddisp))
            {
                xw.WriteStartElement(XML_DebugDep);
                xw.WriteAttributeString(XML_DebugDep_Name_Attr, obj.getRelativePath());
                if (!(obj is VirtualBuildObject))
                {
                    string hash = BuildEngine.theEngine.Repository.GetHash(obj);
                    if (string.IsNullOrEmpty(hash))
                    {
                        // REVIEW: Can this happen?  Do something else here?
                        hash = "unknown";
                    }

                    xw.WriteAttributeString(
                        XML_DebugDep_Hash_Attr,
                        hash);
                }

                xw.WriteEndElement();
            }

            Util.Assert(ddisp == DependencyDisposition.Complete);
        }
    }
}
