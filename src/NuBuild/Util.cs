//--
// <copyright file="Util.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Diagnostics;
    using System.IO;
    using System.Runtime.Remoting.Metadata.W3cXsd2001;
    using System.Security.Cryptography;
    using System.Text;
    using System.Threading;

    /// <summary>
    /// General Utility Functions.
    /// </summary>
    public class Util
    {
        // Win32 MAX_PATH is 260 according to Internets.
        private const int MAX_MUNGED_LENGTH = 150;

        public static string hashString(string input)
        {
            byte[] buffer = new byte[input.Length * sizeof(char)];
            System.Buffer.BlockCopy(input.ToCharArray(), 0, buffer, 0, buffer.Length);
            SHA256Managed hasher = new SHA256Managed();
            byte[] rawHash = hasher.ComputeHash(buffer);
            return new SoapHexBinary(rawHash).ToString();
        }

        public static string hashFilesystemPath(string filesystemPath)
        {
            ////Logger.WriteLine("Hashing " + filesystemPath);
            using (FileStream stream = File.OpenRead(filesystemPath))
            {
                SHA256 sha = new SHA256Managed();
                byte[] rawHash = sha.ComputeHash(stream);
                string rc = new SoapHexBinary(rawHash).ToString();
                ////Logger.WriteLine("fresh hash of " + obj.getFilesystemPath() + " yields " + rc);
                return rc;
            }
        }

        public static string mungeClean(string s)
        {
            StringBuilder sb = new StringBuilder();
            bool lastIsLetter = false;
            foreach (char c in s)
            {
                if (char.IsLetter(c) || char.IsNumber(c))
                {
                    sb.Append(c);
                    lastIsLetter = true;
                }
                else
                {
                    if (lastIsLetter)
                    {
                        sb.Append('-');
                    }

                    lastIsLetter = false;
                }
            }

            if (sb.Length > MAX_MUNGED_LENGTH)
            {
                string originalPathHash = Util.hashString(sb.ToString());
                int additionsLength = originalPathHash.Length + 3;
                sb.Remove(MAX_MUNGED_LENGTH - additionsLength, sb.Length - (MAX_MUNGED_LENGTH - additionsLength));
                sb.Append("...");
                sb.Append(originalPathHash);
            }

            return sb.ToString();
        }

        // Replace characters in a filename the same way DafnySpec/DafnyCC does.
        public static string dafnySpecMungeName(string s)
        {
            return s.Replace('.', '_').Replace('-', '_');
        }

        // Returns null if s doesn't end with eold.
        public static string replaceExtension(string s, string eold, string enew)
        {
            if (s.EndsWith(eold))
            {
                return s.Substring(0, s.Length - eold.Length) + enew;
            }
            else
            {
                return null;
            }
        }

        /// <summary>
        /// Check an ASCII encoded file for the presence of bad characters
        /// and character combinations.  What we consider bad:
        ///  - Tab characters.
        ///  - Carraige returns not followed by a line feed.
        ///  - Line feeds not preceeded by a carraige return.
        /// </summary>
        /// <param name="sourcePath">File to check.</param>
        /// <returns>True if no bad characters found.  False otherwise.</returns>
        public static bool CheckSourceFileForBadCharacters(string sourcePath)
        {
            const int HT = 0x09;  // Horizontal tab.
            const int LF = 0x0a;  // Line feed.
            const int CR = 0x0d;  // Carraige return.

            using (StreamReader reader = new StreamReader(sourcePath))
            {
                int octet;

                // REVIEW: Sanity check reader.CurrentEncoding here?
                while ((octet = reader.Read()) > 0)
                {
                    switch (octet)
                    {
                        case CR:
                            if (reader.Read() != LF)
                            {
                                return false;
                            }

                            break;

                        case LF:
                        case HT:
                            return false;
                    }
                }
            }

            return true;
        }

        public static void Assert(bool condition)
        {
            if (!condition)
            {
                Logger.WriteLine("Assert failure.");
                Debug.Assert(condition);

                for (int loop = 10; loop > 0; loop--)
                {
                    Logger.WriteLine("Something broke in assert.  Attach a debugger to debug.");
                    Logger.WriteLine(string.Format("You have {0} seconds to comply.", loop * 10));
                    Debugger.Break();
                    Thread.Sleep(10000);
                }

                Environment.Exit(-1);
            }
        }
    }
}
