using System;
using System.Net;

namespace IronRSLKVClient
{
  public class Params
  {
    private string serviceFileName;
    private int numThreads;
    private ulong experimentDuration;
    private double setFraction;
    private double deleteFraction;
    private bool verbose;

    public Params()
    {
      serviceFileName = "";
      numThreads = 1;
      experimentDuration = 60;
      setFraction = 0.05;
      deleteFraction = 0.25;
      verbose = false;
    }

    public string ServiceFileName { get { return serviceFileName; } }
    public int NumThreads { get { return numThreads; } }
    public ulong ExperimentDuration { get { return experimentDuration; } }
    public double SetFraction { get { return setFraction; } }
    public double DeleteFraction { get { return deleteFraction; } }
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
        if (serviceFileName.Length == 0) {
          serviceFileName = arg;
          return true;
        }
        else {
          Console.WriteLine("Invalid argument {0}", arg);
          return false;
        }
      }
      var key = arg.Substring(0, pos).ToLower();
      var value = arg.Substring(pos + 1);
      return SetValue(key, value);
    }

    private bool SetValue(string key, string value)
    {
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
          return true;
        }
        catch (Exception e) {
          Console.WriteLine("Could not parse number of threads {0} as a number. Exception:\n{1}", value, e);
          return false;
        }
      }

      if (key == "duration") {
        experimentDuration = Convert.ToUInt64(value);
        return true;
      }

      if (key == "setfraction") {
        try {
          setFraction = Convert.ToDouble(value);
          return true;
        }
        catch (Exception e) {
          Console.WriteLine("Could not parse set fraction {0} as a number. Exception:\n{1}", value, e);
          return false;
        }
      }

      if (key == "deletefraction") {
        try {
          deleteFraction = Convert.ToDouble(value);
          return true;
        }
        catch (Exception e) {
          Console.WriteLine("Could not parse delete fraction {0} as a number. Exception:\n{1}", value, e);
          return false;
        }
      }

      Console.WriteLine("Invalid argument key {0}", key);
      return false;
    }
  }
}
