using System;
using System.Collections.Generic;
using System.IO;
using System.Net;
using System.Text.RegularExpressions;

namespace CreateIronServiceCert
{
  public class Params
  {
    private static int MAX_SERVER_COUNT = 1000;
    private string serviceName;
    private string serviceType;
    private int maxServerIndex;
    private string outputDir;
    private Dictionary<int, string> serverPublicAddrs;
    private Dictionary<int, int> serverPublicPorts;
    private Dictionary<int, string> serverLocalAddrs;
    private Dictionary<int, int> serverLocalPorts;
    private bool verbose;

    public Params()
    {
      serviceName = "MyIronfleetService";
      serviceType = "IronRSLKV";
      maxServerIndex = 0;
      outputDir = ".";
      serverPublicAddrs = new Dictionary<int, string>();
      serverPublicPorts = new Dictionary<int, int>();
      serverLocalAddrs = new Dictionary<int, string>();
      serverLocalPorts = new Dictionary<int, int>();
      verbose = false;
    }

    public int MaxServerIndex { get { return maxServerIndex; } }
    public string ServiceName { get { return serviceName; } }
    public string ServiceType { get { return serviceType; } }
    public string OutputDir { get { return outputDir; } }
    public bool Verbose { get { return verbose; } }

    public bool GetServerData (int serverIndex, out string publicAddr, out int publicPort,
                               out string localAddr, out int localPort)
    {
      publicAddr = "";
      publicPort = 0;
      localAddr = "";
      localPort = 0;
      if (!serverPublicAddrs.TryGetValue(serverIndex, out publicAddr)) {
        return false;
      }
      if (!serverPublicPorts.TryGetValue(serverIndex, out publicPort)) {
        return false;
      }
      if (!serverLocalAddrs.TryGetValue(serverIndex, out localAddr)) {
        localAddr = "localhost";
      }
      if (!serverLocalPorts.TryGetValue(serverIndex, out localPort)) {
        localPort = publicPort;
      }
      return true;
    }

    public bool UseServerIndex(int serverIndex)
    {
      if (serverIndex >= MAX_SERVER_COUNT) {
        Console.WriteLine("ERROR - Server #{0} too big -- must be less than {1}", serverIndex, MAX_SERVER_COUNT);
        return false;
      }
      if (serverIndex == 0) {
        Console.WriteLine("ERROR - Server indices should start at 1, not 0.  So, don't use addr0 or port0.");
        return false;
      }

      maxServerIndex = Math.Max(maxServerIndex, serverIndex);
      return true;
    }

    public bool Validate()
    {
      if (maxServerIndex == 0)
      {
        Console.WriteLine("ERROR - No server data supplied. You need to provide at least addr1 and port1.");
        return false;
      }

      for (int serverIndex = 1; serverIndex <= maxServerIndex; ++serverIndex) {
        if (!serverPublicAddrs.ContainsKey(serverIndex)) {
          Console.WriteLine("ERROR - Missing addr{0}", serverIndex);
          return false;
        }
        if (!serverPublicPorts.ContainsKey(serverIndex)) {
          Console.WriteLine("ERROR - Missing port{0}", serverIndex);
          return false;
        }
      }
      return true;
    }

    public bool ProcessCommandLineArgument(string arg)
    {
      var pos = arg.IndexOf("=");
      if (pos < 0) {
        Console.WriteLine("ERROR - Invalid argument {0}", arg);
        return false;
      }
      var key = arg.Substring(0, pos).ToLower();
      var value = arg.Substring(pos + 1);
      return SetValue(key, value);
    }

    private bool SetValue(string key, string value)
    {
      if (key == "name") {
        serviceName = value;
        return true;
      }

      if (key == "type") {
        serviceType = value;
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

      if (key == "outputdir") {
        outputDir = value;
        try {
          Directory.CreateDirectory(outputDir);
        }
        catch (Exception e) {
          Console.WriteLine("ERROR - Can't create requested output directory {0}", outputDir);
          return false;
        }
      }

      Match m = Regex.Match(key, @"^addr(\d+)$");
      if (m.Success) {
        if (value.Length == 0) {
          Console.WriteLine("ERROR - Address {0} cannot be empty", key);
          return false;
        }
        int serverIndex = Convert.ToInt32(m.Groups[1].Value);
        if (!UseServerIndex(serverIndex)) {
          return false;
        }
        serverPublicAddrs[serverIndex] = value;
        maxServerIndex = Math.Max(maxServerIndex, serverIndex);
        return true;
      }

      m = Regex.Match(key, @"^port(\d+)$");
      if (m.Success) {
        int port;
        try {
          port = Convert.ToInt32(value);
        }
        catch (Exception e) {
          Console.WriteLine("ERROR - Invalid port number {0} given for key {1}", value, key);
          return false;
        }
        if (port == 0 || port > 65535) {
          Console.WriteLine("ERROR - Invalid port number {0} given for key {1}", value, key);
          return false;
        }

        int serverIndex = Convert.ToInt32(m.Groups[1].Value);
        if (!UseServerIndex(serverIndex)) {
          return false;
        }
        
        serverPublicPorts[serverIndex] = port;
        return true;
      }

      m = Regex.Match(key, @"^localaddr(\d+)$");
      if (m.Success) {
        if (value.Length == 0) {
          Console.WriteLine("ERROR - Local address {0} cannot be empty", key);
          return false;
        }
        int serverIndex = Convert.ToInt32(m.Groups[1].Value);
        if (!UseServerIndex(serverIndex)) {
          return false;
        }
        serverLocalAddrs[serverIndex] = value;
        maxServerIndex = Math.Max(maxServerIndex, serverIndex);
        return true;
      }

      m = Regex.Match(key, @"^localport(\d+)$");
      if (m.Success) {
        int port;
        try {
          port = Convert.ToInt32(value);
        }
        catch (Exception e) {
          Console.WriteLine("ERROR - Invalid port number {0} given for key {1}", value, key);
          return false;
        }
        if (port < 1 || port > 65535) {
          Console.WriteLine("ERROR - Port number {0} given for key {1} is not in range 1-65535", value, key);
          return false;
        }

        int serverIndex = Convert.ToInt32(m.Groups[1].Value);
        if (!UseServerIndex(serverIndex)) {
          return false;
        }
        
        serverLocalPorts[serverIndex] = port;
        return true;
      }

      Console.WriteLine("ERROR - Invalid argument key {0}", key);
      return false;
    }
  }
}
