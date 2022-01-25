using System;
using System.Collections.Generic;
using System.IO;
using System.Net;
using System.Text.RegularExpressions;

namespace TestIoFramework
{
  public class Params
  {
    private string serviceFileName;
    private string privateKeyFileName;
    private string localHostNameOrAddress;
    private int localPort;
    private bool verbose;

    public Params()
    {
      serviceFileName = "";
      privateKeyFileName = "";
      localHostNameOrAddress = "";
      localPort = 0;
    }

    public string ServiceFileName { get { return serviceFileName; } }
    public string PrivateKeyFileName { get { return privateKeyFileName; } }
    public string LocalHostNameOrAddress { get { return localHostNameOrAddress; } }
    public int LocalPort { get { return localPort; } }
    public bool Verbose { get { return verbose; } }

    public bool Validate()
    {
      if (serviceFileName.Length == 0) {
        Console.WriteLine("ERROR - Missing service parameter");
        return false;
      }
      if (privateKeyFileName.Length == 0) {
        Console.WriteLine("ERROR - Missing private parameter");
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
        else if (privateKeyFileName.Length == 0) {
          privateKeyFileName = arg;
          return true;
        }
        else {
          Console.WriteLine("ERROR - Invalid argument {0}", arg);
          return false;
        }
      }
      var key = arg.Substring(0, pos).ToLower();
      var value = arg.Substring(pos + 1);
      return SetValue(key, value);
    }

    private bool SetValue(string key, string value)
    {
      if (key == "addr") {
        localHostNameOrAddress = value;
        return true;
      }

      if (key == "port") {
        try {
          localPort = Convert.ToInt32(value);
          return true;
        }
        catch (Exception e) {
          Console.WriteLine("ERROR - Could not convert port {0} to a number. Exception:\n{1}", value, e);
          return false;
        }
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

      Console.WriteLine("ERROR - Invalid argument key {0}", key);
      return false;
    }
  }
}
