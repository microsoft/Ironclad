

namespace IronfleetShtClient
{
  using System;
  using System.Collections.Generic;
  using System.Diagnostics;
  using System.IO;
  using System.Linq;
  using System.Net;
  using System.Text;
  using System.Threading.Tasks;
  using StackExchange.Redis;

    public class Program
    {
        private static int Usage(int errorCode)
        {
            var console = 0 == errorCode ? Console.Out : Console.Error;
            console.WriteLine("usage: [SERVICE_TYPE] [SERVICE_IP] [SERVICE_PORT] [THREAD_COUNT] [DURATION_SECS]");
            return errorCode;
        }

        public static int Main(string[] args)
        {
            IPEndPoint serviceEndpoint;
            int threadCount;
            long experimentDuration;
            int valueBytes;

            if (args.Length != 6)
            {
                Console.Error.WriteLine("incorrect number of arguments ({0})", args.Length);
                return Usage(-1);
            }

            if (args[0].Trim().ToLowerInvariant() != "redis")
            {
                Console.Error.WriteLine("only 'redis' type is currently supported ('{0}' requested)", args[0].Trim());
                return Usage(-1);
            }

            try
            {
                serviceEndpoint = new IPEndPoint(IPAddress.Parse(args[1]), Convert.ToInt32(args[2]));
                threadCount = Convert.ToInt32(args[3]);
                experimentDuration = Convert.ToInt64(args[4]) * 1000;
                valueBytes = Convert.ToInt32(args[5]);
            }
            catch (Exception e)
            {
                Console.Error.WriteLine("Command line exception: " + e);
                return Usage(-2);
            }

            Console.Out.WriteLine("serviceEndpoint: {0}", serviceEndpoint);
            Console.Out.WriteLine("threadCount: {0}", threadCount);
            Console.Out.WriteLine("experimentDuration: {0} ms", experimentDuration);
            Console.Out.WriteLine("valueBytes: {0}", valueBytes);

            // Create a directory for logging all of our output
            string guid = Guid.NewGuid().ToString();
            string outputDirectory = String.Format("{0}\\IronfleetOutput\\Job-{1}", Environment.GetEnvironmentVariable("TMP"), guid);
            Directory.CreateDirectory(outputDirectory);

            // Create the log file itself
            var log = new FileStream(outputDirectory + "\\client.txt", FileMode.Create);
            var logStream = new StreamWriter(log);
            var rng = new Random();

            Func<KeyValueStoreClient> connect = () => RedisClient.Connect(serviceEndpoint);
            var dog = new StrawDog(connect, threadCount, experimentDuration, valueBytes, rng, logStream);

            Console.Out.WriteLine("[[READY]]");
            Console.Out.WriteLine("ClientGUID {0}", guid);
            
            dog.Perform(rng);

            Console.Out.WriteLine("[[DONE]]");
            Console.Out.Flush();
            logStream.Flush();

            return 0;
        }
    }
}
