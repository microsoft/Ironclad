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
      Console.Write(@"
Usage:  dotnet IronRSLKVClient.dll [key=value]...

Allowed keys:
  clientip - IP address this client should bind to (default 127.0.0.1)
  clientport - Port this client should bind to (default 6000)
  ip1 - IP address of first IronRSLKVServer (default 127.0.0.1)
  ip2 - IP address of second IronRSLKVServer (default 127.0.0.1)
  ip3 - IP address of third IronRSLKVServer (default 127.0.0.1)
  port1 - port of first IronRSLKVServer (default 4001)
  port2 - port of first IronRSLKVServer (default 4002)
  port3 - port of first IronRSLKVServer (default 4003)
  nthreads - number of client threads to run (default 1)
  duration - duration of experiment in seconds (default 60)
  initialseqno - first sequence number each thread uses (default 0)
  setfraction - fraction of requests that are sets (default 0.25)
  deletefraction - fraction of requests that are deletes (default 0.05)

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
      ulong num_threads = 1;
      ulong experiment_duration = 60;
      IPAddress client_ip = IPAddress.Parse("127.0.0.1");
      IPAddress ip1 = IPAddress.Parse("127.0.0.1");
      IPAddress ip2 = IPAddress.Parse("127.0.0.1");
      IPAddress ip3 = IPAddress.Parse("127.0.0.1");
      int client_port = 6000;
      int port1 = 4001;
      int port2 = 4002;
      int port3 = 4003;
      ulong initial_seq_no = 0;
      double set_fraction = 0.05;
      double delete_fraction = 0.25;

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
              num_threads = Convert.ToUInt64(value);
              break;
            case "duration" :
              experiment_duration = Convert.ToUInt64(value);
              break;
            case "initialseqno" :
              initial_seq_no = Convert.ToUInt64(value);
              break;
            case "setfraction" :
              set_fraction = Convert.ToDouble(value);
              break;
            case "deletefraction" :
              delete_fraction = Convert.ToDouble(value);
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

      Client.endpoints = new List<IPEndPoint>() {
        new IPEndPoint(ip1, port1), new IPEndPoint(ip2, port2), new IPEndPoint(ip3, port3) };
      Client.my_addr = client_ip;

      HiResTimer.Initialize();
      Client.Trace("Client process starting " + num_threads + " running for "+ experiment_duration + "s ...");
            
      Console.WriteLine("[[READY]]");
            
      TextWriter stdout = Console.Out;

      // Start the experiment
      var threads = Client.StartThreads<Client>(num_threads, client_port, initial_seq_no, set_fraction, delete_fraction).ToArray();

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
