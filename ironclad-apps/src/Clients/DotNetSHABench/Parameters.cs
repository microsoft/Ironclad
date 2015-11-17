using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace DotNetSHABench
{
    class InvalidParameterException : Exception
    {
        public string contents;
        public InvalidParameterException(string i_contents) { contents = i_contents; }
    }

    public class Parameters
    {
        public static int messageSize = 2048;
        public static int numberOfRuns = 100;

        public static void Print()
        {
            Console.Error.WriteLine("messageSize\t{0}", messageSize);
            Console.Error.WriteLine("numberOfRuns\t{0}", numberOfRuns);
        }

        public static void PrintUsage()
        {
            Console.Out.WriteLine("Usage:  DotNetSHABench.exe [filename or param=value]... where filename contains");
            Console.Out.WriteLine("        lines of the form param=value and param must be one of the following.");
            Console.Out.WriteLine();
            Console.Out.WriteLine("  messageSize                  = message size, in bytes");
            Console.Out.WriteLine("  numberOfRuns                 = number of times to advance counter");
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

            if (String.Compare(parameter, "messageSize", StringComparison.OrdinalIgnoreCase) == 0)
            {
                Parameters.messageSize = Convert.ToInt32(value);
            }
            else if (String.Compare(parameter, "numberOfRuns", StringComparison.OrdinalIgnoreCase) == 0)
            {
                Parameters.numberOfRuns = Convert.ToInt32(value);
            }
            else
            {
                throw new InvalidParameterException("Invalid command-line parameter " + parameter);
            }
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
