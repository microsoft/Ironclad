using Common;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace PassHash
{
    class InvalidParameterException : Exception
    {
        public string contents;
        public InvalidParameterException(string i_contents) { contents = i_contents; }
    }

    public class Parameters
    {
        public static int passwordLength = 12;
        public static int saltLength = 16;

        public static void Print()
        {
            CommonParams.Print();
            Console.Error.WriteLine("passwordLength\t{0}", passwordLength);
            Console.Error.WriteLine("saltLength\t{0}", saltLength);
        }

        public static void PrintUsage()
        {
            Console.Out.WriteLine("Usage:  PassHash.exe [filename or param=value]... where filename contains");
            Console.Out.WriteLine("        lines of the form param=value and param must be one of the following.");
            Console.Out.WriteLine();
            CommonParams.PrintUsage();
            Console.Out.WriteLine("  passwordLength               = length of password to use");
            Console.Out.WriteLine("  saltLength                   = length of salt to use");
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
            if (String.Compare(parameter, "passwordLength", StringComparison.OrdinalIgnoreCase) == 0)
            {
                Parameters.passwordLength = Convert.ToInt32(value);
                return;
            }
            if (String.Compare(parameter, "saltLength", StringComparison.OrdinalIgnoreCase) == 0)
            {
                Parameters.saltLength = Convert.ToInt32(value);
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
