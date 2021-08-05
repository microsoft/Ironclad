using IronfleetCommon;
using IronfleetIoFramework;
using MathNet.Numerics.Distributions;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text.Json;
using System.Threading;

namespace IronLockServer
{
  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet IronLockServer.dll [key=value]...

Allowed keys:
  service   - file name containing service description
  private   - file name containing private key
  verbose   - use verbose output
");
    }

    static void Main(string[] args)
    {
      Console.WriteLine("IronLockServer program started");

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
        return;
      }

      string json;

      try {
        json = File.ReadAllText(ps.ServiceFileName);
      }
      catch (Exception e) {
        Console.WriteLine("ERROR - Could not read contents of service file {0}. Exception:\n{1}", ps.ServiceFileName, e);
        return;
      }

      ServiceIdentity serviceIdentity;
      try {
        serviceIdentity = JsonSerializer.Deserialize<ServiceIdentity>(json);
      }
      catch (Exception e) {
        Console.WriteLine("ERROR - Could not deserialize contents of service file {0}. Exception:\n{1}",
                          ps.ServiceFileName, e);
        return;
      }

      if (serviceIdentity.ServiceType != "IronLock") {
        Console.WriteLine("ERROR - Service file {0} contains description of service of type {1}, not IronLock.",
                          ps.ServiceFileName, serviceIdentity.ServiceType);
        return;
      }

      try {
        json = File.ReadAllText(ps.PrivateKeyFileName);
      }
      catch (Exception e) {
        Console.WriteLine("ERROR - Could not read contents of private key file {0}. Exception:\n{1}", ps.PrivateKeyFileName, e);
        return;
      }

      PrivateIdentity privateIdentity;
      try {
        privateIdentity = JsonSerializer.Deserialize<PrivateIdentity>(json);
      }
      catch (Exception e) {
        Console.WriteLine("ERROR - Could not deserialize contents of private key file {0}. Exception:\n{1}",
                          ps.PrivateKeyFileName, e);
        return;
      }

      var nc = Native____Io__s_Compile.NetClient.Create(privateIdentity, serviceIdentity.Servers, ps.Verbose);
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
