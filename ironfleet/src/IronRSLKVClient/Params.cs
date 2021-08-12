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
    private bool printRequestsAndReplies;

    public Params()
    {
      serviceFileName = "";
      numThreads = 1;
      experimentDuration = 60;
      setFraction = 0.05;
      deleteFraction = 0.25;
      verbose = false;
      printRequestsAndReplies = false;
    }

    public string ServiceFileName { get { return serviceFileName; } }
    public int NumThreads { get { return numThreads; } }
    public ulong ExperimentDuration { get { return experimentDuration; } }
    public double SetFraction { get { return setFraction; } }
    public double DeleteFraction { get { return deleteFraction; } }
    public bool PrintRequestsAndReplies { get { return printRequestsAndReplies; } }
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

    private bool SetBoolValue(string key, string value, ref bool p)
    {
      if (value == "false") {
        p = false;
        return true;
      }
      else if (value == "true") {
        p = true;
        return true;
      }
      else {
        Console.WriteLine("ERROR - Invalid {0} value {1} - should be false or true", key, value);
        return false;
      }
    }

    private bool SetValue(string key, string value)
    {
      if (key == "verbose") {
        return SetBoolValue(key, value, ref verbose);
      }

      if (key == "print") {
        return SetBoolValue(key, value, ref printRequestsAndReplies);
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
