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
    private bool profile;
    private bool progress;
    private bool verbose;
    private bool safeguard;

    public Params()
    {
      serviceFileName = "";
      privateKeyFileName = "";
      localHostNameOrAddress = "";
      localPort = 0;
      profile = false;
      progress = false;
      verbose = false;
      safeguard = true;
    }

    public string ServiceFileName { get { return serviceFileName; } }
    public string PrivateKeyFileName { get { return privateKeyFileName; } }
    public string LocalHostNameOrAddress { get { return localHostNameOrAddress; } }
    public int LocalPort { get { return localPort; } }
    public bool Profile { get { return profile; } }
    public bool Progress { get { return progress; } }
    public bool Verbose { get { return verbose; } }
    public bool Safeguard { get { return safeguard; } }

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

      if (key == "profile") {
        return SetBoolValue(key, value, ref profile);
      }

      if (key == "progress") {
        return SetBoolValue(key, value, ref progress);
      }

      if (key == "verbose") {
        return SetBoolValue(key, value, ref verbose);
      }

      if (key == "safeguard") {
        return SetBoolValue(key, value, ref safeguard);
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
Usage:  dotnet IronRSL{0}Server.dll <service> <private> [key=value]...

  <service> - file path of the service description
  <private> - file path of the private key

Allowed keys:
  addr      - local host name or address to listen to (default:
              whatever's specified in the private key file)
  port      - port to listen to (default: whatever's specified
              in the private key file)
  profile   - print profiling info (false or true, default: false)
  progress  - print progress (false or true, default: false)
  verbose   - use verbose output (false or true, default: false)
  safeguard - delete the private key file after reading it to
              prevent running the same instance twice (false or
              true, default: true [see below])

You should only run an instance of this server once, since we haven't
implemented crash recovery.  To prevent you from accidentally running
it multiple times, this program deletes its private key file right
after reading it.  You can override this behavior with
safeguard=false, but this is a VERY UNSAFE thing to do.

Fortunately, IronRSL can deal with the failure of fewer than half its
servers.  But, if half of them or more fail, you'll have to create a
new service.  That is, you'll have to start over by running
CreateIronServiceCerts, and that new service will be in its initial
state.
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

      Native____Io__s_Compile.PrintParams.SetParameters(ps.Profile, ps.Progress);

      if (ps.Safeguard) {
        File.Delete(ps.PrivateKeyFileName);
        Console.WriteLine("Deleted private key file after reading it since RSL servers should never run twice.");
      }
      else {
        Console.WriteLine(@"
  *** DANGER:  Because you specified safeguard=false, we didn't delete the ***
  *** private key file to prevent you from running the RSL server twice.   ***
  *** Hopefully, you're just testing things.                               ***
");
      }

      var nc = Native____Io__s_Compile.NetClient.Create(privateIdentity, ps.LocalHostNameOrAddress, ps.LocalPort,
                                                        serviceIdentity.Servers, ps.Verbose, serviceIdentity.UseSsl);
      Dafny.ISequence<byte>[] serverPublicKeys =
        serviceIdentity.Servers.Select(server => Dafny.Sequence<byte>.FromArray(IoScheduler.HashPublicKey(server.PublicKey))).ToArray();
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
