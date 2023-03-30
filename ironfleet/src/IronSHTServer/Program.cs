using IronfleetCommon;
using IronfleetIoFramework;
using MathNet.Numerics.Distributions;
using System;
using System.Linq;
using System.Numerics;
using System.Threading;

namespace IronSHTServer
{
  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet IronSHTServer.dll <service> <private> [key=value]...

  <service> - file path of the service description
  <private> - file path of the private key

Allowed keys:
  addr      - local host name or address to listen to (default:
              whatever's specified in the private key file)
  port      - port to listen to (default: whatever's specified
              in the private key file)
  profile   - print profiling info (false or true, default: false)
  verbose   - use verbose output (false or true, default: false)
");
    }

    static void Main(string[] args)
    {
      Console.WriteLine("IronSHTServer program started");

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
      if (serviceIdentity.ServiceType != "IronSHT") {
        Console.Error.WriteLine("ERROR - Service described by {0} is of type {1}, not IronSHT", ps.ServiceFileName,
                                serviceIdentity.ServiceType);
        return;
      }

      PrivateIdentity privateIdentity = PrivateIdentity.ReadFromFile(ps.PrivateKeyFileName);
      if (privateIdentity == null) {
        return;
      }

      Native____Io__s_Compile.PrintParams.SetParameters(ps.Profile, i_shouldPrintProgress: false);

      var nc = Native____Io__s_Compile.NetClient.Create(privateIdentity, ps.LocalHostNameOrAddress, ps.LocalPort,
                                                        serviceIdentity.Servers, ps.Verbose, serviceIdentity.UseSsl);
      Dafny.ISequence<byte>[] serverPublicKeys =
        serviceIdentity.Servers.Select(server => Dafny.Sequence<byte>.FromArray(nc.HashPublicKey(server.PublicKey))).ToArray();
      var ironArgs = Dafny.Sequence<Dafny.ISequence<byte>>.FromArray(serverPublicKeys);

      Profiler.Initialize();
      Native____Io__s_Compile.Time.Initialize();
      Console.WriteLine("IronFleet program started.");
      Console.WriteLine("[[READY]]");
      Main__i_Compile.__default.IronfleetMain(nc, ironArgs);
      Console.WriteLine("[[EXIT]]");
    }
  }
}
