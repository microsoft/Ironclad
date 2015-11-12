//--
// <copyright file="AnnotationScanner.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;
    using System.Text;
    using System.Text.RegularExpressions;

    internal class AnnotationScanner
    {
        private BuildObject inputObject;
        private List<string[]> annotations;
        private bool complete;

        // Constructor for emitting new/code-assembled annotations.
        public AnnotationScanner()
        {
            this.inputObject = null;
            this.annotations = new List<string[]>();
            this.complete = false;
        }

        public AnnotationScanner(BuildObject inputObject)
        {
            this.inputObject = inputObject;
            this.annotations = new List<string[]>();
            Regex re = new Regex("<NuBuild([^>]*)/>");
            using (TextReader tr = BuildEngine.theEngine.Repository.OpenRead(inputObject))
            {
                while (true)
                {
                    string line = tr.ReadLine();
                    if (line == null)
                    {
                        break;
                    }

                    Match match = re.Match(line);
                    if (match.Success)
                    {
                        string[] arguments = match.Groups[1].ToString().Split(null).Where(s => s.Length > 0).ToArray();
                        this.annotations.Add(arguments);
                    }
                }
            }

            this.complete = true;
        }

        public void addAnnotation(string[] annotation)
        {
            Util.Assert(!this.complete);
            this.annotations.Add(annotation);
        }

        public string emit(string commentToken)
        {
            this.complete = true;
            StringBuilder sb = new StringBuilder();
            foreach (string[] annotation in this.annotations)
            {
                sb.AppendLine(commentToken + "<NuBuild " + string.Join(" ", annotation) + " />");
            }

            return sb.ToString();
        }

        public IEnumerable<string[]> getAnnotations(string label)
        {
            return this.annotations.Where(sa => sa[0].Equals(label));
        }

        // Look for 0 or 1 instance of a single-valued annotation.
        public string getTheAnnotation(string label, string defaultValue)
        {
            IEnumerable<string[]> anns = this.getAnnotations(label);
            if (anns.Count() == 0)
            {
                return defaultValue;
            }

            string[] ann = anns.First();
            if (ann.Length != 2)
            {
                throw new SourceConfigurationError(
                    string.Format(
                        "Annotation {0} in file {1} should have exactly one argument",
                        ann[0],
                        this.inputObject.getRelativePath()));
            }

            return ann[1];
        }

        internal static void transferAnnotations(WorkingDirectory workingDirectory, BuildObject source, BuildObject dest, string commentToken)
        {
            new AnnotationScanner(source).injectAnnotations(workingDirectory, dest, commentToken);
        }

        // REVIEW: Make this private?
        internal void injectAnnotations(WorkingDirectory workingDirectory, BuildObject dest, string commentToken)
        {
            string annotations = this.emit(commentToken);

            // REVIEW: Improve upon this round-about way of prepending to a file?
            string destStr = File.ReadAllText(workingDirectory.PathTo(dest));
            File.Delete(workingDirectory.PathTo(dest));
            File.WriteAllText(workingDirectory.PathTo(dest), annotations + destStr);
        }
    }
}
