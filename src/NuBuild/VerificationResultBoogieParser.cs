//--
// <copyright file="VerificationResultBoogieParser.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Text.RegularExpressions;

    internal class VerificationResultBoogieParser : IVerificationResultParser
    {
        private static Regex dispositionTimeoutsRegex = new Regex("Boogie program verifier finished with (\\d*) verified, (\\d*) errors*, (\\d) time outs*");
        private static Regex dispositionNoTimeoutsRegex = new Regex("Boogie program verifier finished with (\\d*) verified, (\\d*) errors*");
        private static Regex dispositionParseErrorRegex = new Regex("Error opening file");
        private static Regex dispositionParseError2Regex = new Regex("(\\d*) parse errors detected in");
        private static Regex dispositionParseError3Regex = new Regex("(\\d*) type checking errors detected in");
        private static Regex dispositionParseError4Regex = new Regex("(\\d*) name resolution errors detected in");
        private static Regex dispositionProverDiedRegex = new Regex("Prover error: Prover died");

        public void parseOutput(string output, out int parseFailures, out int verificationFailures, out int timeouts)
        {
            parseFailures = 0;
            verificationFailures = 0;
            timeouts = 0;

            Match match = dispositionTimeoutsRegex.Match(output);
            if (match.Success)
            {
                ////int succeeding_methods = Int32.Parse(m.Groups[1].ToString());
                verificationFailures = Int32.Parse(match.Groups[2].ToString());
                timeouts = Int32.Parse(match.Groups[3].ToString());
                return;
            }

            match = dispositionNoTimeoutsRegex.Match(output);
            if (match.Success)
            {
                ////int succeeding_methods = Int32.Parse(m.Groups[1].ToString());
                verificationFailures = Int32.Parse(match.Groups[2].ToString());
                return;
            }

            match = dispositionParseErrorRegex.Match(output);
            if (match.Success)
            {
                parseFailures = 1;
                return;
            }

            match = dispositionParseError2Regex.Match(output);
            if (match.Success)
            {
                parseFailures = Int32.Parse(match.Groups[1].ToString());
                return;
            }

            match = dispositionParseError3Regex.Match(output);
            if (match.Success)
            {
                parseFailures = Int32.Parse(match.Groups[1].ToString());
                return;
            }

            match = dispositionParseError4Regex.Match(output);
            if (match.Success)
            {
                parseFailures = Int32.Parse(match.Groups[1].ToString());
                return;
            }

            match = dispositionProverDiedRegex.Match(output);
            if (match.Success)
            {
                parseFailures = 1;
                return;
            }

            parseFailures = 1;
            ////throw new Exception("Unable to parse Dafny output");
        }
    }
}
