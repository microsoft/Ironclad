namespace IronfleetTestDriver
{
    using System;
    using System.Linq;
    using System.Numerics;
    using System.Threading;
    using System.IO;
    using System.Net;
    using System.Collections.Generic;

    class Program
    {

        static void usage()
        {
          Console.Write(@"
Usage:  dotnet IronSHTClient.dll [key=value]...

Allowed keys:
  clientip - IP address this client should bind to (default 127.0.0.1)
  clientport - Port this client should bind to (default 6000)
  ip1 - IP address of first IronSHTServer (default 127.0.0.1)
  ip2 - IP address of second IronSHTServer (default 127.0.0.1)
  ip3 - IP address of third IronSHTServer (default 127.0.0.1)
  port1 - port of first IronSHTServer (default 4001)
  port2 - port of first IronSHTServer (default 4002)
  port3 - port of first IronSHTServer (default 4003)
  nthreads - number of experiment client threads to run, not
             counting the setup thread (default 1)
  duration - duration of experiment in seconds (default 60)
  workload - g for Gets, s for Sets, f for Sharding (default s)
  numkeys - number of keys (default 1000)
  valsize - number of bytes in each value (default 1024)

Each thread will use a different port number, using consecutive port
numbers starting with clientport. For instance, if nthreads=3 and
clientport=6000, then the setup thread will use port 6000 and the 3
experiment threads will use ports 6001-6003.

NOTE: Each client endpoint is expected to follow a certain stateful
protocol. So if you run this program multiple times, either: (1) use
a different clientip or (2) use a clientport that causes different
ports to be used.
");
        }

        static void Main(string[] args)
        {            
            uint num_threads = 1;
            ulong experiment_duration = 60;
            IPAddress client_ip = IPAddress.Parse("127.0.0.1");
            IPAddress ip1 = IPAddress.Parse("127.0.0.1");
            IPAddress ip2 = IPAddress.Parse("127.0.0.1");
            IPAddress ip3 = IPAddress.Parse("127.0.0.1");
            int client_port = 6000;
            int port1 = 4001;
            int port2 = 4002;
            int port3 = 4003;
            char workload = 's';
            ulong num_keys = 1000;
            ulong size_value = 1024;

            foreach (var arg in args)
            {
                var pos = arg.IndexOf("=");
                if (pos < 0) {
                    Console.WriteLine("Invalid argument {0}", arg);
                    usage();
                    return;
                }
                var key = arg.Substring(0, pos).ToLower();
                var value = arg.Substring(pos + 1);
                try {
                    switch (key) {
                        case "clientip" :
                            client_ip = IPAddress.Parse(value);
                            break;
                        case "ip1" :
                            ip1 = IPAddress.Parse(value);
                            break;
                        case "ip2" :
                            ip2 = IPAddress.Parse(value);
                            break;
                        case "ip3" :
                            ip3 = IPAddress.Parse(value);
                            break;
                        case "clientport" :
                            client_port = Convert.ToInt32(value);
                            break;
                        case "port1" :
                            port1 = Convert.ToInt32(value);
                            break;
                        case "port2" :
                            port2 = Convert.ToInt32(value);
                            break;
                        case "port3" :
                            port3 = Convert.ToInt32(value);
                            break;
                        case "nthreads" :
                            num_threads = Convert.ToUInt32(value);
                            break;
                        case "duration" :
                            experiment_duration = Convert.ToUInt64(value);
                            break;
                        case "workload" :
                          if (value != "g" && value != "s" && value != "f") {
                                Console.WriteLine("Workload must be 'g', 's', or 'f', but you specified {0}", arg);
                                usage();
                                return;
                            }
                            workload = value[0];
                            break;
                        case "numkeys" :
                            num_keys = Convert.ToUInt64(value);
                            break;
                        case "valuesize" :
                            size_value = Convert.ToUInt64(value);
                            break;
                        default :
                            Console.WriteLine("Invalid argument {0}", arg);
                            usage();
                            return;
                    }
                }
                catch (Exception e) {
                    Console.WriteLine("Invalid value {0} for key {1}, leading to exception:\n{2}", value, key, e);
                    usage();
                    return;
                }
            }

            ClientBase.endpoints = new List<IPEndPoint>() {
                new IPEndPoint(ip1, port1), new IPEndPoint(ip2, port2), new IPEndPoint(ip3, port3) };
            ClientBase.my_addr = client_ip;

            HiResTimer.Initialize();
            IronSHT.Client.Trace("Client process starting " + num_threads + " running for " + experiment_duration + " s ...");

            Console.WriteLine("[[READY]]");

            // Setup the system
            uint num_setup_threads = 1;
            var setup_threads = ClientBase.StartSetupThreads<IronSHT.Client>(client_port, num_setup_threads, num_keys, size_value).ToArray();
            setup_threads[0].Join();
            Console.WriteLine("[[SETUP COMPLETE]]");

            // Start the experiment
            var threads = ClientBase.StartExperimentThreads<IronSHT.Client>(client_port + (int)num_setup_threads, num_threads, num_keys, size_value, workload).ToArray();

            if (experiment_duration == 0)
            {
                threads[0].Join();
            }
            else
            {
                Thread.Sleep((int)experiment_duration * 1000);
                Console.Out.WriteLine("[[DONE]]");
                Console.Out.Flush();
                Environment.Exit(0);
            }
        }
    }
}
