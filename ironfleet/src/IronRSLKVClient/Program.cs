﻿using IronfleetCommon;
using IronfleetIoFramework;
using System;
using System.Linq;
using System.Numerics;
using System.Threading;
using System.IO;
using System.Net;
using System.Collections.Generic;

namespace IronRSLKVClient
{
  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet IronRSLKVClient.dll [key=value]...

Allowed keys:
  service        - file name containing service description (required)
  nthreads       - number of client threads to run (default 1)
  duration       - duration of experiment in seconds (default 60)
  setfraction    - fraction of requests that are sets (default 0.25)
  deletefraction - fraction of requests that are deletes (default 0.05)
  verbose        - print verbose output (false or true, default false)
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

      if (!ps.Validate()) {
        usage();
        return;
      }

      var serviceIdentity = ServiceIdentity.ReadFromFile(ps.ServiceFileName);

      HiResTimer.Initialize();
      if (ps.Verbose) {
        Console.WriteLine("Client process starting {0} threads running for {1} s...", ps.NumThreads, ps.ExperimentDuration);
      }
            
      Console.WriteLine("[[READY]]");
            
      // Start the experiment
      var threads = Client.StartThreads<Client>(ps, serviceIdentity).ToArray();

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
