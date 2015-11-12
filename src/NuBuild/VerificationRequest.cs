//--
// <copyright file="VerificationRequest.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    internal class VerificationRequest
    {
        public VerifyMode verifyMode;
        public List<string> selectiveVerifyModuleNames;

        public VerificationRequest()
        {
            this.verifyMode = VerifyMode.Verify;
            this.selectiveVerifyModuleNames = new List<string>();
        }

        public enum VerifyMode
        {
            Verify,
            NoSymDiff,
            SelectiveVerify,
            NoVerify
        }

        public enum SymDiffMode
        {
            UseSymDiff,
            NoSymDiff
        }

        public bool isComplete()
        {
            return this.verifyMode == VerifyMode.Verify;
        }

        public override string ToString()
        {
            if (this.verifyMode == VerifyMode.SelectiveVerify)
            {
                return this.verifyMode.ToString() + "(" + string.Join(",", this.selectiveVerifyModuleNames) + ")";
            }
            else
            {
                return this.verifyMode.ToString();
            }
        }

        public SymDiffMode getSymDiffMode()
        {
            return this.verifyMode == VerifyMode.Verify ? SymDiffMode.UseSymDiff : SymDiffMode.NoSymDiff;
        }
    }
}
