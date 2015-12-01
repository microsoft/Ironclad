//--
// <copyright file="VerificationResultFStarParser.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Text.RegularExpressions;

    internal class VerificationResultFStarParser : IVerificationResultParser
    {
        private static readonly Regex success = CreateRegex("^All verification conditions discharged successfully$");
        private static readonly Regex errorCount = CreateRegex("^Error: (\\d+) errors were reported (see above)$");

        public void parseOutput(string output, out int parseFailures, out int verificationFailures, out int timeouts)
        {
            parseFailures = 0;
            verificationFailures = 0;
            timeouts = 0;

            Match match = errorCount.Match(output);
            if (match.Success)
            {
                verificationFailures = Int32.Parse(match.Groups[1].ToString());
            }

            match = success.Match(output);
            if (match.Success)
            {
                return;
            }

            parseFailures = 1;
            Logger.WriteLine("[NuBuild] Unrecognized F* output; will report as a single parsing failure.");
        }

        private static Regex CreateRegex(string pattern)
        {
            return new Regex(pattern, RegexOptions.Compiled | RegexOptions.CultureInvariant | RegexOptions.Multiline);
        }
    }
}
