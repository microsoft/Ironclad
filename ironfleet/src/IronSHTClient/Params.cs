using System;
using System.Net;

namespace IronSHTClient
{
  public class Params
  {
    private string serviceFileName;
    private int numSetupThreads;
    private int numThreads;
    private ulong experimentDuration;
    private char workload;
    private int numKeys;
    private int valueSize;
    private bool verbose;

    public Params()
    {
      serviceFileName = "";
      numSetupThreads = 1;
      numThreads = 1;
      experimentDuration = 60;
      workload = 's';
      numKeys = 1000;
      valueSize = 1000;
      verbose = false;
    }

    public string ServiceFileName { get { return serviceFileName; } }
    public int NumSetupThreads { get { return numSetupThreads; } }
    public int NumThreads { get { return numThreads; } }
    public ulong ExperimentDuration { get { return experimentDuration; } }
    public char Workload { get { return workload; } }
    public int NumKeys { get { return numKeys; } }
    public int ValueSize { get { return valueSize; } }
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

      if (key == "workload") {
        if (value != "g" && value != "s" && value != "f") {
          Console.WriteLine("Workload must be 'g', 's', or 'f', but you specified {0}", value);
          return false;
        }
        workload = value[0];
        return true;
      }

      if (key == "numkeys") {
        numKeys = Convert.ToInt32(value);
        if (numKeys < 1) {
          Console.WriteLine("Number of keys must be greater than zero, not {0}", value);
          return false;
        }
        return true;
      }

      if (key == "valuesize") {
        valueSize = Convert.ToInt32(value);
        if (valueSize < 0 || valueSize >= 1024) {
          Console.WriteLine("Value size must be non-negative and less than 1024, but you specified {0}", valueSize);
          return false;
        }
        return true;
      }

      Console.WriteLine("Invalid argument key {0}", key);
      return false;
    }
  }
}
