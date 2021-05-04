using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Numerics;
using System.Threading;

namespace IronSHTClient
{
  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet IronSHTClient.dll [key=value]...

Allowed keys:
  client         - IP address+port of client (default 127.0.0.1:6000)
  server1        - IP address+port of first server (default 127.0.0.1:4001)
  server2        - IP address+port of second server (default 127.0.0.1:4002)
  server3        - IP address+port of third server (default 127.0.0.1:4003)
  nthreads       - number of experiment client threads to run, not
                   counting the setup thread (default 1)
  duration       - duration of experiment in seconds (default 60)
  initialseqno   - first sequence number each thread uses (default 0)
  workload       - g for Gets, s for Sets, f for Sharding (default s)
  numkeys        - number of keys (default 1000)
  valsize        - number of bytes in each value (default 1024)
  verbose        - print verbose output (false or true, default false)

Each thread will use a different port number, using consecutive port
numbers starting with the one in client. For instance, if nthreads=3
and client=127.0.0.1:6000, then the setup thread will use port 6000
and the 3 experiment threads will use ports 6001-6003.

NOTE: Each client endpoint is expected to follow a certain stateful
protocol. So if you run this program multiple times, either: (1) use
a different clientip or (2) use a clientport that causes different
ports to be used.
");
    }

    static void Main(string[] args)
    {
      Params ps = new Params();

      foreach (var arg in args)
      {
        if (!ps.ProcessCommandLineArgument(arg)) {
          usage();
          return;
        }
      }

      HiResTimer.Initialize();
      if (ps.verbose) {
        Console.WriteLine("Client process starting {0} threads running for {1} s...", ps.numThreads, ps.experimentDuration);
      }

      Console.WriteLine("[[READY]]");

      // Setup the system
      var setupThreads = Client.StartSetupThreads(ps).ToArray();
      setupThreads[0].Join();
      Console.WriteLine("[[SETUP COMPLETE]]");

      // Start the experiment
      var threads = Client.StartExperimentThreads(ps).ToArray();

      if (ps.experimentDuration == 0)
      {
        threads[0].Join();
      }
      else
      {
        Thread.Sleep((int)ps.experimentDuration * 1000);
        Console.Out.WriteLine("[[DONE]]");
        Console.Out.Flush();
        Environment.Exit(0);
      }
    }
  }
}
