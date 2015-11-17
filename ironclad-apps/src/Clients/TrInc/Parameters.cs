using Common;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace TrInc
{
    class InvalidParameterException : Exception
    {
        public string contents;
        public InvalidParameterException(string i_contents) { contents = i_contents; }
    }

    public class Parameters
    {
        public static int messageLength = 32;
        public static int publicKeyBits = 2048;

        public static void Print()
        {
            CommonParams.Print();
            Console.Error.WriteLine("messageLength\t{0}", messageLength);
            Console.Error.WriteLine("publicKeyBits\t{0}", publicKeyBits);
        }

        public static void PrintUsage()
        {
            Console.Out.WriteLine("Usage:  TrInc.exe [filename or param=value]... where filename contains");
            Console.Out.WriteLine("        lines of the form param=value and param must be one of the following.");
            Console.Out.WriteLine();
            CommonParams.PrintUsage();
            Console.Out.WriteLine("  messageLength                = length of message to attest");
            Console.Out.WriteLine("  publicKeyBits                = bits in our counter's public key");
        }

        public static void ApplyArguments (string[] args)
        {
            try
            {
                foreach (string arg in args)
                {
                    ApplyArgument(arg);
                }
            }
            catch (InvalidParameterException e)
            {
                Console.Out.WriteLine(e.contents);
                Parameters.PrintUsage();
                Environment.Exit(-1);
            }
        }

        public static void ApplyArgument (string arg)
        {
            char[] splitter = {'='};
            string[] sp = arg.ToLower().Split(splitter);

            if (sp.Length == 1)
            {
                ApplyArgumentsInFile(arg);
                return;
            }
            else if (sp.Length != 2)
            {
                throw new InvalidParameterException("Invalid command-line argument " + arg);
            }

            string parameter = sp[0];
            string value = sp[1];

            if (CommonParams.ApplyArgument(parameter, value))
            {
                return;
            }
            if (String.Compare(parameter, "messageLength", StringComparison.OrdinalIgnoreCase) == 0)
            {
                Parameters.messageLength = Convert.ToInt32(value);
                return;
            }
            if (String.Compare(parameter, "publicKeyBits", StringComparison.OrdinalIgnoreCase) == 0)
            {
                Parameters.publicKeyBits = Convert.ToInt32(value);
                return;
            }
            if (String.Compare(parameter, "numberOfRuns", StringComparison.OrdinalIgnoreCase) == 0)
            {
                CommonParams.numberOfRuns = Convert.ToInt32(value);
                return;
            }
            if (String.Compare(parameter, "ignoreKey", StringComparison.OrdinalIgnoreCase) == 0)
            {
                CommonParams.ignoreKey = Convert.ToInt32(value) != 0;
                return;
            }

            throw new InvalidParameterException("Invalid command-line parameter " + parameter);
        }

        public static void ApplyArgumentsInFile(string filename)
        {
            string[] args = File.ReadAllLines(filename);
            foreach (string arg in args)
            {
                ApplyArgument(arg);
            }
        }
    }
}
