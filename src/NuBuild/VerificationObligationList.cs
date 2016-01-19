//--
// <copyright file="VerificationObligationList.cs" company="Microsoft Corporation">
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
    using System.Threading.Tasks;

    internal class VerificationObligationList
    {
        public const string VOL_EXTN = ".vol";  // VOL = Verification Object List

        private readonly List<BuildObject> verificationObligations;
        private bool complete;

        public VerificationObligationList()
        {
            this.verificationObligations = new List<BuildObject>();
        }

        public VerificationObligationList(IEnumerable<BuildObject> data)
        {
            this.verificationObligations = new List<BuildObject>(data);
            this.complete = true;
        }

        public static VerificationObligationList fetch(BuildObject obj)
        {
            VerificationObligationList vol = new VerificationObligationList();
            using (TextReader sr = BuildEngine.theEngine.Repository.OpenRead(obj))
            {
                string line;
                while ((line = sr.ReadLine()) != null)
                {
                    Util.Assert(!line.StartsWith(BuildEngine.theEngine.getSrcRoot()));   // unimplemented
                    Util.Assert(!line.StartsWith(BuildEngine.theEngine.getVirtualRoot()));   // nonsense
                    vol.Add(new BuildObject(line));
                }
            }

            vol.complete = true;
            return vol;
        }

        public void Add(BuildObject obj)
        {
            Util.Assert(!this.complete);
            this.verificationObligations.Add(obj);
        }

        public IEnumerable<BuildObject> getVerificationObligations()
        {
            Util.Assert(this.complete);
            return this.verificationObligations;
        }

        public void store(WorkingDirectory workingDirectory, BuildObject location)
        {
            this.complete = true;
            string[] lines = this.verificationObligations.Select(vo => vo.getRelativePath()).ToArray();
            File.WriteAllLines(workingDirectory.PathTo(location), lines);
        }
    }
}
