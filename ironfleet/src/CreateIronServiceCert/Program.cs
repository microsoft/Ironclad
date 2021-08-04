using IronfleetIoFramework;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Numerics;
using System.Text.Json;
using System.Threading;

namespace CreateIronServiceCert
{
  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet CreateIronServiceCert.dll [key=value]...

Allowed keys:
  name         - friendly name of the service (default ""MyIronfleetService"")
  type         - service type (default ""IronRSLKV"")
  outputdir    - directory to write certificates into (default ""."")
  addr<n>      - public address (host name or IP) of server #<n>
  port<n>      - public port of server #<n>
  localaddr<n> - local address of server #<n> (default same as addr<n>)
  localport<n> - local port of server #<n> (default same as port<n>)
  verbose      - print verbose output (false or true, default false)
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
      string json;

      for (int serverIndex = 1; serverIndex <= ps.MaxServerIndex; ++serverIndex) {
        string publicAddr, localAddr;
        int publicPort, localPort;
        if (!ps.GetServerData(serverIndex, out publicAddr, out publicPort, out localAddr, out localPort)) {
          Console.WriteLine("ERROR - Missing data for server #{0}", serverIndex);
          return;
        }

        PublicIdentity publicIdentity;
        PrivateIdentity privateIdentity;
        string serverName = string.Format("{0}.{1}.server{2}", ps.ServiceName, ps.ServiceType, serverIndex);
        bool result = IronfleetCrypto.CreateIdentity(serverName, publicAddr, publicPort, localAddr, localPort,
                                                     out publicIdentity, out privateIdentity);

        try {
          json = JsonSerializer.Serialize<PrivateIdentity>(privateIdentity);
        }
        catch (Exception e) {
          Console.WriteLine("ERROR - Could not serialize private key data for server {0}. Exception:\n{1}", serverIndex, e);
          return;
        }

        var privateKeyFileName = Path.Join(ps.OutputDir,
                                           string.Format("{0}.{1}.server{2}.private.txt", ps.ServiceName,
                                                         ps.ServiceType, serverIndex));
        try {
          File.WriteAllText(privateKeyFileName, json);
        }
        catch (Exception e) {
          Console.WriteLine("ERROR - Could not create file {0}. Exception:\n{1}", privateKeyFileName, e);
          return;
        }

        Console.WriteLine("Successfully wrote private key for server {0} to {1}", serverIndex, privateKeyFileName);
        serverPublicIdentities.Add(publicIdentity);
      }

      var serviceIdentity = new ServiceIdentity {
        FriendlyName = ps.ServiceName,
        ServiceType = ps.ServiceType,
        Servers = serverPublicIdentities
      };
      try {
        json = JsonSerializer.Serialize<ServiceIdentity>(serviceIdentity);
      }
      catch (Exception e) {
        Console.WriteLine("ERROR - Could not serialize service identity. Exception:\n{0}", e);
        return;
      }

      var serviceFileName = Path.Join(ps.OutputDir, string.Format("{0}.{1}.service.txt", ps.ServiceName, ps.ServiceType));
      try {
        File.WriteAllText(serviceFileName, json);
      }
      catch (Exception e) {
        Console.WriteLine("ERROR - Could not write service identity to file {0}. Exception:\n{1}", serviceFileName, e);
        return;
      }

      Console.WriteLine("Successfully wrote service description to {0}", serviceFileName);
      Console.WriteLine("DONE - SUCCESS");
    }
  }
}
