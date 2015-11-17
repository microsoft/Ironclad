using Common;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace DiffPriv
{
    class InvalidParameterException : Exception
    {
        public string contents;
        public InvalidParameterException(string i_contents) { contents = i_contents; }
    }

    public class Parameters
    {
        public static int numColumns = 4;
        public static int maxColumnValue = 2048;
        public static int numRows = 105;
        public static int numQueries = 105;
        public static int nonceBytes = 20;

        public static void Print()
        {
            CommonParams.Print();
            Console.Error.WriteLine("numColumns\t{0}", numColumns);
            Console.Error.WriteLine("maxColumnValue\t{0}", maxColumnValue);
            Console.Error.WriteLine("numRows\t{0}", numRows);
            Console.Error.WriteLine("numQueries\t{0}", numQueries);
            Console.Error.WriteLine("nonceBytes\t{0}", nonceBytes);
        }

        public static void PrintUsage()
        {
            Console.Out.WriteLine("Usage:  DiffPriv.exe [filename or param=value]... where filename contains");
            Console.Out.WriteLine("        lines of the form param=value and param must be one of the following.");
            Console.Out.WriteLine();
            CommonParams.PrintUsage();
            Console.Out.WriteLine("  numColumns                   = number of columns in each row");
            Console.Out.WriteLine("  maxColumnValue               = maximum value in each column");
            Console.Out.WriteLine("  numRows                      = number of rows to add");
            Console.Out.WriteLine("  numQueries                   = number of queries to run");
            Console.Out.WriteLine("  nonceBytes                   = number of bytes to use in each row nonce");
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
            if (String.Compare(parameter, "numColumns", StringComparison.OrdinalIgnoreCase) == 0)
            {
                Parameters.numColumns = Convert.ToInt32(value);
                return;
            }
            if (String.Compare(parameter, "maxColumnValue", StringComparison.OrdinalIgnoreCase) == 0)
            {
                Parameters.maxColumnValue = Convert.ToInt32(value);
                return;
            }
            if (String.Compare(parameter, "numRows", StringComparison.OrdinalIgnoreCase) == 0)
            {
                Parameters.numRows = Convert.ToInt32(value);
                return;
            }
            if (String.Compare(parameter, "numQueries", StringComparison.OrdinalIgnoreCase) == 0)
            {
                Parameters.numQueries = Convert.ToInt32(value);
                return;
            }
            if (String.Compare(parameter, "nonceBytes", StringComparison.OrdinalIgnoreCase) == 0)
            {
                Parameters.nonceBytes = Convert.ToInt32(value);
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
