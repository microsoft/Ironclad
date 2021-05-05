using IronfleetCommon;
using System;
using System.Linq;
using System.Numerics;
using System.Threading;
using System.IO;
using System.Net;
using System.Collections.Generic;

namespace IronRSLCounterClient
{
  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet IronRSLCounterClient.dll [key=value]...

Allowed keys:
  clientport     - Port this client should bind to (default 6000)
  server1        - IP address+port of first server (default 127.0.0.1:4001)
  server2        - IP address+port of second server (default 127.0.0.1:4002)
  server3        - IP address+port of third server (default 127.0.0.1:4003)
  nthreads       - number of client threads to run (default 1)
  duration       - duration of experiment in seconds (default 60)
  verbose        - print verbose output (false or true, default false)

If nthreads > 1, then each thread will use a different port number,
using consecutive port numbers starting with clientport.

NOTE: Each client endpoint is expected to use strictly increasing
sequence numbers. So if you run this program multiple times, either:
(1) use a different clientip, (2) use a clientport that causes
different ports to be used, or (3) use an initialseqno greater than
any sequence number seen in previous runs (e.g., if the previous run
output #req100, use at least initialseqno=101)
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
            
      // Start the experiment
      var threads = Client.StartThreads<Client>(ps).ToArray();

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
