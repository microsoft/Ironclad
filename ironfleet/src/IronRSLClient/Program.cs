using System;
using System.Linq;
using System.Numerics;
using System.Threading;
using System.IO;
using System.Net;
using System.Collections.Generic;

namespace IronRSLClient
{
    class Program
    {
        static void usage()
        {
            Console.WriteLine("Expected usage: clientIP IP0 port0 IP1 port1 IP2 port2 num_threads duration_secs [send_reqs_at_once]");
        }

        static void Main(string[] args)
        {            
            if (args.Length < 9)
            {
                usage();
                return;
            }

            ulong num_threads = 1;
            ulong experiment_duration = 60;
            IPAddress client_ip;
            IPEndPoint ip0;
            IPEndPoint ip1;
            IPEndPoint ip2;
            bool send_reqs_at_once = false;

            try
            {
                client_ip = IPAddress.Parse(args[0]);
                ip0 = new IPEndPoint(IPAddress.Parse(args[1]), Convert.ToInt32(args[2]));
                ip1 = new IPEndPoint(IPAddress.Parse(args[3]), Convert.ToInt32(args[4]));
                ip2 = new IPEndPoint(IPAddress.Parse(args[5]), Convert.ToInt32(args[6]));

                num_threads = Convert.ToUInt64(args[7]);
                experiment_duration = Convert.ToUInt64(args[8]);

                if (args.Length > 9)
                {
                    send_reqs_at_once = true;
                }
            }
            catch (Exception e)
            {
                Console.WriteLine("Command line exception: " + e);
                usage();
                return;
            }

            ClientBase.endpoints = new List<IPEndPoint>() { ip0, ip1, ip2 };
            ClientBase.my_addr = client_ip;

            HiResTimer.Initialize();
            Client.Trace("Client process starting " + num_threads + " running for "+ experiment_duration + "s ...");
            
            Console.WriteLine("[[READY]]");
            
            // Redirect all subsequent output to the log
            TextWriter stdout = Console.Out;

            // Start the experiment
            var threads = ClientBase.StartThreads<Client>(num_threads, send_reqs_at_once).ToArray();

            if (experiment_duration == 0)
            {
                threads[0].Join();
            }
            else
            {
                Thread.Sleep((int)experiment_duration * 1000);
                stdout.WriteLine("[[DONE]]");
                stdout.Flush();
                Environment.Exit(0);
            }
        }
    }
}
