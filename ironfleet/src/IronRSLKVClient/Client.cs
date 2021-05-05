using IronfleetCommon;
using IronfleetIoFramework;
using KVMessages;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Text;
using System.Threading;

namespace IronRSLKVClient
{
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
  
    private static KVRequest GetRandomRequest(Random rng, Params ps)
    {
      int keySelector = rng.Next(26);
      char k = (char)('a' + keySelector);
      StringBuilder keyBuilder = new StringBuilder();
      keyBuilder.Append(k);
      keyBuilder.Append(k);
      keyBuilder.Append(k);
      string key = keyBuilder.ToString();
      
      int reqTypeSelector = rng.Next();
      if (reqTypeSelector < ps.setFraction * Int32.MaxValue) {
        char v = (char)('A' + keySelector);
        StringBuilder valBuilder = new StringBuilder();
        valBuilder.Append(v);
        valBuilder.Append(v);
        valBuilder.Append(v);
        valBuilder.Append(v);
        valBuilder.Append(rng.Next(100000));
        string val = valBuilder.ToString();
        if (ps.verbose) {
          Console.WriteLine("Submitting set request for {0} => {1}", key, val);
        }
        return new KVSetRequest(key, val);
      }
      else if (reqTypeSelector < (ps.setFraction + ps.deleteFraction) * Int32.MaxValue) {
        if (ps.verbose) {
          Console.WriteLine("Submitting delete request for {0}", key);
        }
        return new KVDeleteRequest(key);
      }
      else {
        if (ps.verbose) {
          Console.WriteLine("Submitting get request for {0}", key);
        }
        return new KVGetRequest(key);
      }
    }

    private void Run()
    {
      IPEndPoint myEndpoint = new IPEndPoint(IPAddress.Parse("127.0.0.1"), ps.clientPort + (int)id);
      RSLClient rslClient = new RSLClient(ps.serverEps, myEndpoint);

      Thread.Sleep(3000);

      Random rng = new Random();

      for (int requestNum = 1; true; ++requestNum)
      {
        KVRequest request = GetRandomRequest(rng, ps);
        byte[] requestBytes = request.Encode();
        var startTime = HiResTimer.Ticks;
        byte[] replyBytes = rslClient.SubmitRequest(requestBytes, ps.verbose);
        var endTime = HiResTimer.Ticks;
        KVReply reply = KVReply.Decode(replyBytes, 0);

        if (ps.verbose) {
          Console.WriteLine("Received reply of type {0}", reply.ReplyType);
          if (reply is KVGetFoundReply gfr) {
            Console.WriteLine("Value obtained for get was {0}", gfr.Val);
          }
        }
        // Report time in milliseconds, since that's what the Python script appears to expect
        Console.WriteLine("#req{0} {1} {2} {3}",
                          requestNum,
                          HiResTimer.TicksToMilliseconds(startTime),
                          HiResTimer.TicksToMilliseconds(endTime),
                          id);
      }
    }
  }
}
