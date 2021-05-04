using System;
using System.Net;

namespace IronRSLKVClient
{
  public class Params
  {
    public int numThreads;
    public ulong experimentDuration;
    public IPEndPoint[] serverEps;
    public int clientPort;
    public ulong initialSeqNum;
    public double setFraction;
    public double deleteFraction;
    public bool verbose;

    public Params()
    {
      numThreads = 1;
      experimentDuration = 60;
      serverEps = new IPEndPoint[3] { IPEndPoint.Parse("127.0.0.1:4001"),
                                      IPEndPoint.Parse("127.0.0.1:4002"),
                                      IPEndPoint.Parse("127.0.0.1:4003") };
      clientPort = 6000;
      initialSeqNum = 0;
      setFraction = 0.05;
      deleteFraction = 0.25;
      verbose = false;
    }

    public bool ProcessCommandLineArgument(string arg)
    {
      var pos = arg.IndexOf("=");
      if (pos < 0) {
        Console.WriteLine("Invalid argument {0}", arg);
        return false;
      }
      var key = arg.Substring(0, pos).ToLower();
      var value = arg.Substring(pos + 1);
      return SetValue(key, value);
    }

    private IPEndPoint ResolveIPEndpoint(string s)
    {
      var pos = s.IndexOf(":");
      if (pos < 0)
      {
        Console.WriteLine("Invalid endpoint descriptor {0} (no colon found)", s);
        return null;
      }

      string host = s.Substring(0, pos);
      int port = Convert.ToInt32(s.Substring(pos + 1));
      foreach (var addr in Dns.GetHostEntry(host).AddressList)
      {
        if (addr.AddressFamily == System.Net.Sockets.AddressFamily.InterNetwork)
        {
          return new IPEndPoint(addr, port);
        }
      }

      Console.WriteLine("Could not resolve host name {0} in server endpoint descriptor {1}", host, s);
      return null;
    }

    private bool SetValue(string key, string value)
    {
      try {
        switch (key) {
          case "clientport" :
            clientPort = Convert.ToInt32(value);
            return true;

          case "server1" :
            serverEps[0] = ResolveIPEndpoint(value);
            return serverEps[0] != null;

          case "server2" :
            serverEps[1] = ResolveIPEndpoint(value);
            return serverEps[1] != null;

          case "server3" :
            serverEps[2] = ResolveIPEndpoint(value);
            return serverEps[2] != null;

          case "nthreads" :
            numThreads = Convert.ToInt32(value);
            if (numThreads < 1) {
              Console.WriteLine("Number of threads must be at least 1, so can't be {0}", numThreads);
              return false;
            }
            return true;

          case "duration" :
            experimentDuration = Convert.ToUInt64(value);
            return true;

          case "initialseqno" :
            initialSeqNum = Convert.ToUInt64(value);
            return true;

          case "setfraction" :
            setFraction = Convert.ToDouble(value);
            return true;

          case "deletefraction" :
            deleteFraction = Convert.ToDouble(value);
            return true;

          case "verbose" :
            if (value == "false") {
              verbose = false;
              return true;
            }
            if (value == "true") {
              verbose = true;
              return true;
            }
            Console.WriteLine("Invalid verbose value {0} - should be false or true", value);
            return false;
        }
      }
      catch (Exception e) {
        Console.WriteLine("Invalid value {0} for key {1}, leading to exception:\n{2}", value, key, e);
        return false;
      }

      Console.WriteLine("Invalid argument key {0}", key);
      return false;
    }
  }
}
