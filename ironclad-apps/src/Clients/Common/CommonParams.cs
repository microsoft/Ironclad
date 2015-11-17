using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Common
{
    public class CommonParams
    {
        public static string hostname = "localhost";
        public static int port = 1983;
        public static int numberOfRuns = 105;
        public static bool ignoreKey = false;
        public static string loaderHash = "6768033E216468247BD031A0A2D9876D79818F8F";
        public static string appHash = "";
        public static int serverKeyBits = 2048;
        public static bool printValues = true;

        public static void Print()
        {
            Console.Error.WriteLine("hostname\t{0}", hostname);
            Console.Error.WriteLine("port\t{0}", port);
            Console.Error.WriteLine("numberOfRuns\t{0}", numberOfRuns);
            Console.Error.WriteLine("ignoreKey\t{0}", ignoreKey);
            Console.Error.WriteLine("loaderHash\t{0}", loaderHash);
            Console.Error.WriteLine("appHash\t{0}", appHash);
            Console.Error.WriteLine("serverKeyBits\t{0}", serverKeyBits);
            Console.Error.WriteLine("printValues\t{0}", printValues);
        }

        public static void PrintUsage()
        {
            Console.Out.WriteLine("  hostname                     = host name of the TrInc service");
            Console.Out.WriteLine("  port                         = port that the TrInc service listens to");
            Console.Out.WriteLine("  numberOfRuns                 = number of times to run each benchmark");
            Console.Out.WriteLine("  ignoreKey                    = 1 means ignore the public key and don't do any checking using it");
            Console.Out.WriteLine("  loaderHash                   = hex value of SHA-1 of loader, e.g., 01EF..23CD");
            Console.Out.WriteLine("  appHash                      = hex value of SHA-1 of app, e.g., 01EF..23CD");
            Console.Out.WriteLine("  serverKeyBits                = number of bits for server key");
            Console.Out.WriteLine("  printValues                  = 1 means print all profile values, 0 means just print aggregates");
        }

        public static bool ApplyArgument (string parameter, string value)
        {
            if (String.Compare(parameter, "hostname", StringComparison.OrdinalIgnoreCase) == 0)
            {
                CommonParams.hostname = value;
                return true;
            }
            if (String.Compare(parameter, "port", StringComparison.OrdinalIgnoreCase) == 0)
            {
                CommonParams.port = Convert.ToInt32(value);
                return true;
            }
            if (String.Compare(parameter, "numberOfRuns", StringComparison.OrdinalIgnoreCase) == 0)
            {
                CommonParams.numberOfRuns = Convert.ToInt32(value);
                return true;
            }
            if (String.Compare(parameter, "ignoreKey", StringComparison.OrdinalIgnoreCase) == 0)
            {
                CommonParams.ignoreKey = (Convert.ToInt32(value) != 0);
                return true;
            }
            if (String.Compare(parameter, "loaderHash", StringComparison.OrdinalIgnoreCase) == 0)
            {
                CommonParams.loaderHash = value;
                return true;
            }
            if (String.Compare(parameter, "appHash", StringComparison.OrdinalIgnoreCase) == 0)
            {
                CommonParams.appHash = value;
                return true;
            }
            if (String.Compare(parameter, "serverKeyBits", StringComparison.OrdinalIgnoreCase) == 0)
            {
                CommonParams.serverKeyBits = Convert.ToInt32(value);
                return true;
            }
            if (String.Compare(parameter, "printValues", StringComparison.OrdinalIgnoreCase) == 0)
            {
                CommonParams.printValues = (Convert.ToInt32(value) != 0);
                return true;
            }
            return false;
        }
    }
}
