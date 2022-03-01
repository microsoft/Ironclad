using IronfleetIoFramework;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Numerics;
using System.Threading;

namespace CreateIronServiceCerts
{
  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet CreateIronServiceCerts.dll [key=value]...

Allowed keys:
  name         - friendly name of the service (default ""MyIronfleetService"")
  type         - service type (default ""IronRSLKV"")
  outputdir    - directory to write certificates into (default ""."")
  addr<n>      - public address (host name or IP) of server #<n>
  port<n>      - public port of server #<n>
  verbose      - print verbose output (false or true, default false)
  useSSL       - whether to use SSL (default: true)
");
    }

    static void Main(string[] args)
    {
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

      List<PublicIdentity> serverPublicIdentities = new List<PublicIdentity>();

      for (int serverIndex = 1; serverIndex <= ps.MaxServerIndex; ++serverIndex) {
        string addr;
        int port;
        if (!ps.GetServerData(serverIndex, out addr, out port)) {
          Console.WriteLine("ERROR - Missing data for server #{0}", serverIndex);
          return;
        }

        PublicIdentity publicIdentity;
        PrivateIdentity privateIdentity;
        string serverName = string.Format("{0}.{1}.server{2}", ps.ServiceName, ps.ServiceType, serverIndex);
        IronfleetCrypto.CreateNewIdentity(serverName, addr, port, out publicIdentity, out privateIdentity);

        var privateKeyFileName = Path.Join(ps.OutputDir, string.Format("{0}.private.txt", serverName));
        if (!privateIdentity.WriteToFile(privateKeyFileName)) {
          return;
        }
        Console.WriteLine("Successfully wrote private key for server {0} to {1}", serverIndex, privateKeyFileName);

        serverPublicIdentities.Add(publicIdentity);
      }

      var serviceIdentity = new ServiceIdentity {
        FriendlyName = ps.ServiceName,
        ServiceType = ps.ServiceType,
        Servers = serverPublicIdentities,
        UseSsl = ps.UseSsl
      };
      var serviceFileName = Path.Join(ps.OutputDir, string.Format("{0}.{1}.service.txt", ps.ServiceName, ps.ServiceType));
      if (!serviceIdentity.WriteToFile(serviceFileName)) {
        return;
      }
      Console.WriteLine("Successfully wrote service description to {0}", serviceFileName);

      Console.WriteLine("DONE - SUCCESS");
    }
  }
}
