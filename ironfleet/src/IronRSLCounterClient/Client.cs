using IronfleetCommon;
using IronfleetIoFramework;
using System;
using System.Collections.Generic;
using System.IO;
using System.Net;
using System.Threading;
using System.Linq;

namespace IronRSLCounterClient
{
  public class IncrementRequest
  {
    public IncrementRequest() { }

    public byte[] Encode()
    {
      MemoryStream memStream = new MemoryStream();
      IoEncoder.WriteUInt64(memStream, 0);             // request type (0 = increment)
      return memStream.ToArray();
    }
  }

  public class IncrementReply
  {
    public UInt64 counterValue;

    private IncrementReply(UInt64 i_counterValue)
    {
      counterValue = i_counterValue;
    }
    
    public static IncrementReply Decode(byte[] bytes)
    {
      if (bytes.Length != 8) {
        Console.Error.WriteLine("Got invalid-length reply");
        return null;
      }

      UInt64 counterValue = IoEncoder.ExtractUInt64(bytes, 0);
      return new IncrementReply(counterValue);
    }
  }

  public class Client
  {
    public int id;
    public Params ps;

    private Client(int i_id, Params i_ps)
    {
      id = i_id;
      ps = i_ps;
    }

    static public IEnumerable<Thread> StartThreads<T>(Params ps)
    {
      for (int i = 0; i < ps.numThreads; ++i)
      {
        Client c = new Client(i, ps);
        Thread t = new Thread(c.Run);
        t.Start();
        yield return t;
      }
    }

    private void Run()
    {
      IPEndPoint myEndpoint = new IPEndPoint(IPAddress.Parse("127.0.0.1"), ps.clientPort + (int)id);
      RSLClient rslClient = new RSLClient(ps.serverEps, myEndpoint);

      Thread.Sleep(3000);

      for (int requestNum = 1; true; ++requestNum)
      {
        var request = new IncrementRequest();
        byte[] requestBytes = request.Encode();
        var startTime = HiResTimer.Ticks;
        byte[] replyBytes = rslClient.SubmitRequest(requestBytes, ps.verbose);
        var endTime = HiResTimer.Ticks;
        var reply = IncrementReply.Decode(replyBytes);
        if (ps.verbose) {
          Console.WriteLine("Received increment reply with counter {0}", reply.counterValue);
        }
        Console.WriteLine("#req {0} {1} {2}",
                          id,
                          requestNum,
                          HiResTimer.TicksToMilliseconds(endTime - startTime));
      }
    }
  }
}
