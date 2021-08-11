using IronfleetCommon;
using IronfleetIoFramework;
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
Usage:  dotnet IronSHTClient.dll <service> [key=value]...

  <service> - file path of the service description

Allowed keys:
  nthreads  - number of experiment client threads to run, not
              counting the setup thread (default 1)
  duration  - duration of experiment in seconds (default 60)
  workload  - g for Gets, s for Sets, f for Sharding (default s)
  numkeys   - number of keys (default 1000)
  valsize   - number of bytes in each value (default 1024)
  verbose   - print verbose output (false or true, default false)
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

      var serviceIdentity = ServiceIdentity.ReadFromFile(ps.ServiceFileName);
      if (serviceIdentity == null) {
        return;
      }
      if (serviceIdentity.ServiceType != "IronSHT") {
        Console.Error.WriteLine("ERROR - Service described by {0} is of type {1}, not IronSHT", ps.ServiceFileName,
                                serviceIdentity.ServiceType);
        return;
      }

      HiResTimer.Initialize();
      if (ps.Verbose) {
        Console.WriteLine("Client process starting {0} threads running for {1} s...", ps.NumThreads, ps.ExperimentDuration);
      }

      Console.WriteLine("[[READY]]");

      // Setup the system
      var setupThreads = Client.StartSetupThreads(ps, serviceIdentity).ToArray();
      setupThreads[0].Join();
      Console.WriteLine("[[SETUP COMPLETE]]");

      // Start the experiment
      var threads = Client.StartExperimentThreads(ps, serviceIdentity).ToArray();

      if (ps.ExperimentDuration == 0)
      {
        threads[0].Join();
      }
      else
      {
        Thread.Sleep((int)ps.ExperimentDuration * 1000);
        Console.Out.WriteLine("[[DONE]]");
        Console.Out.Flush();
        Environment.Exit(0);
      }
    }
  }
}
