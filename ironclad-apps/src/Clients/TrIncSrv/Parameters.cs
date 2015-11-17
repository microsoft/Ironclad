using Common;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace TrIncSrv
{
    class InvalidParameterException : Exception
    {
        public string contents;
        public InvalidParameterException(string i_contents) { contents = i_contents; }
    }

    public class Parameters
    {
        public static void Print()
        {
            CommonParams.Print();
        }

        public static void PrintUsage()
        {
            Console.Out.WriteLine("Usage:  TrIncSrv.exe [filename or param=value]... where filename contains");
            Console.Out.WriteLine("        lines of the form param=value and param must be one of the following.");
            Console.Out.WriteLine();
            CommonParams.PrintUsage();
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
