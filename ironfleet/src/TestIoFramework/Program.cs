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

    public Runner(ServiceIdentity i_serviceIdentity, PrivateIdentity i_privateIdentity)
    {
      serviceIdentity = i_serviceIdentity;
      privateIdentity = i_privateIdentity;
      scheduler = new IoScheduler(privateIdentity, serviceIdentity.Servers, false);
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

        Console.WriteLine("Sending message {0} to {1}", message, scheduler.PublicKeyToString(serverPublicKey));
        
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
        Console.WriteLine("Received message {0} from {1}", message, scheduler.PublicKeyToString(remote));
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
  service      - file name containing service description
  private      - file name containing private key
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

      var runner = new Runner(serviceIdentity, privateIdentity);
      runner.Run();
    }
  }
}
