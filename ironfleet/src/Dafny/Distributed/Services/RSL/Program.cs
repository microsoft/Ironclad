using IronfleetCommon;
using IronfleetIoFramework;
using IronRSL;
using MathNet.Numerics.Distributions;
using System;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Threading;

namespace IronRSLServer
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
        Console.WriteLine("ERROR - Invalid argument {0}", arg);
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

      if (key == "private") {
        privateKeyFileName = value;
        return true;
      }

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

  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet IronRSL{0}Server.dll [key=value]...

Allowed keys:
  service  - file name containing service description
  private  - file name containing private key
  addr     - local host name or address to listen to (optional)
  port     - port to listen to (optional)
  verbose  - use verbose output

If the optional parameter 'addr' or 'port' is left out,
we use whatever is in the private key file.
", Service.Name);
    }

    static void Main(string[] args)
    {
      Console.WriteLine("IronRSL{0}Server program started", Service.Name);

      Console.WriteLine("Processing command-line arguments");

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

      ServiceIdentity serviceIdentity = ServiceIdentity.ReadFromFile(ps.ServiceFileName);
      if (serviceIdentity == null) {
        return;
      }
      if (serviceIdentity.ServiceType != "IronRSL" + Service.Name) {
        Console.Error.WriteLine("Provided service identity has type {0}, not IronRSL{1}.",
                                serviceIdentity.ServiceType, Service.Name);
        return;
      }

      PrivateIdentity privateIdentity = PrivateIdentity.ReadFromFile(ps.PrivateKeyFileName);
      if (privateIdentity == null) {
        return;
      }

      File.Delete(ps.PrivateKeyFileName);
      Console.WriteLine("Deleted private key file after reading it since RSL servers should never run twice.");

      var nc = Native____Io__s_Compile.NetClient.Create(privateIdentity, ps.LocalHostNameOrAddress, ps.LocalPort,
                                                        serviceIdentity.Servers, ps.Verbose);
      Dafny.ISequence<byte>[] serverPublicKeys =
        serviceIdentity.Servers.Select(server => Dafny.Sequence<byte>.FromArray(server.PublicKey)).ToArray();
      var ironArgs = Dafny.Sequence<Dafny.ISequence<byte>>.FromArray(serverPublicKeys);

      Profiler.Initialize();
      Native____Io__s_Compile.Time.Initialize();
      Console.WriteLine("[[READY]]");
      Main__i_Compile.__default.IronfleetMain(nc, ironArgs);
      Console.WriteLine("[[EXIT]]");
    }
  }
}

namespace AppStateMachine__s_Compile
{
  public partial class AppStateMachine
  {
    Service service;

    internal AppStateMachine(Service i_service)
    {
      service = i_service;
    }

    public static AppStateMachine Initialize()
    {
      return new AppStateMachine(Service.Initialize());
    }

    public static AppStateMachine Deserialize(Dafny.ISequence<byte> state)
    {
      return new AppStateMachine(Service.Deserialize(state.Elements));
    }

    public Dafny.ISequence<byte> Serialize()
    {
      return Dafny.Sequence<byte>.FromArray(service.Serialize());
    }

    public Dafny.ISequence<byte> HandleRequest(Dafny.ISequence<byte> request)
    {
      return Dafny.Sequence<byte>.FromArray(service.HandleRequest(request.Elements));
    }
  }
}
