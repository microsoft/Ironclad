using System;
using System.Net;

namespace IronRSLCounterClient
{
  public class Params
  {
    private string serviceFileName;
    private int numThreads;
    private ulong experimentDuration;
    private bool verbose;

    public Params()
    {
      serviceFileName = "";
      numThreads = 1;
      experimentDuration = 60;
      verbose = false;
    }

    public string ServiceFileName { get { return serviceFileName; } }
    public int NumThreads { get { return numThreads; } }
    public ulong ExperimentDuration { get { return experimentDuration; } }
    public bool Verbose { get { return verbose; } }

    public bool Validate()
    {
      if (serviceFileName.Length == 0) {
        Console.WriteLine("ERROR - Missing service parameter");
        return false;
      }
      return true;
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

    private bool SetValue(string key, string value)
    {
      if (key == "service") {
        serviceFileName = value;
        return true;
      }

      if (key == "verbose") {
        if (value == "false") {
          verbose = false;
          return true;
        }
        if (value == "true") {
          verbose = true;
          return true;
        }
        Console.WriteLine("ERROR - Invalid verbose value {0} - should be false or true", value);
        return false;
      }

      if (key == "nthreads") {
        try {
          numThreads = Convert.ToInt32(value);
          if (numThreads < 1) {
            Console.WriteLine("Number of threads must be at least 1, so can't be {0}", numThreads);
            return false;
          }
        }
        catch (Exception e) {
          Console.WriteLine("Could not parse number of threads {0} as a number. Exception:\n{1}", value, e);
          return false;
        }
        return true;
      }

      if (key == "duration") {
        experimentDuration = Convert.ToUInt64(value);
        return true;
      }

      Console.WriteLine("Invalid argument key {0}", key);
      return false;
    }
  }
}
