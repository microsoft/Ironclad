using IronfleetIoFramework;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Numerics;
using System.Text;
using System.Text.Json;
using System.Threading;

namespace TestIoFramework
{
  class Runner
  {
    private ServiceIdentity serviceIdentity;
    private PrivateIdentity privateIdentity;
    private IoScheduler scheduler;

    public Runner(ServiceIdentity i_serviceIdentity, PrivateIdentity i_privateIdentity, bool i_verbose)
    {
      serviceIdentity = i_serviceIdentity;
      privateIdentity = i_privateIdentity;
      scheduler = new IoScheduler(privateIdentity, serviceIdentity.Servers, i_verbose);
    }

    public void Run()
    {
      Thread t = new Thread(this.SenderThread);
      t.Start();
      this.ReceiverThread();
    }

    private void SenderThread()
    {
      Random rng = new Random();
      while (true) {
        int serverIndex = rng.Next(serviceIdentity.Servers.Count);
        PublicIdentity serverIdentity = serviceIdentity.Servers[serverIndex];
        byte[] serverPublicKey = serverIdentity.PublicKey;

        int randomNumber = rng.Next(10000);
        string message = string.Format("Hello {0}", randomNumber);
        byte[] messageBytes = Encoding.UTF8.GetBytes(message);

        Console.WriteLine("Sending message {0} to {1}", message, IoScheduler.PublicKeyToString(serverPublicKey));
        
        scheduler.SendPacket(serverPublicKey, messageBytes);
        Thread.Sleep(1000);
      }
    }

    private void ReceiverThread()
    {
      while (true) {
        bool ok;
        bool timedOut;
        byte[] remote;
        byte[] messageBytes;
        scheduler.ReceivePacket(0, out ok, out timedOut, out remote, out messageBytes);
        if (!ok) {
          Console.WriteLine("Not OK, so terminating receiver thread");
          return;
        }
        if (timedOut) {
          Thread.Sleep(100);
          continue;
        }
        string message = Encoding.UTF8.GetString(messageBytes);
        Console.WriteLine("Received message {0} from {1}", message, IoScheduler.PublicKeyToString(remote));
      }
    }
  }
  
  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet TestIoFramework.dll [key=value]...

Allowed keys:
  service   - file name containing service description
  private   - file name containing private key
  verbose   - use verbose output
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

      ServiceIdentity serviceIdentity = ServiceIdentity.ReadFromFile(ps.ServiceFileName);
      if (serviceIdentity == null) {
        return;
      }

      PrivateIdentity privateIdentity = PrivateIdentity.ReadFromFile(ps.PrivateKeyFileName);
      if (privateIdentity == null) {
        return;
      }

      var runner = new Runner(serviceIdentity, privateIdentity, ps.Verbose);
      runner.Run();
    }
  }
}
