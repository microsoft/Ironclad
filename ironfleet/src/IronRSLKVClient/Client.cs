using IronfleetCommon;
using IronfleetIoFramework;
using KVMessages;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Net;
using System.Text;
using System.Threading;

namespace IronRSLKVClient
{
  public class RequestMessage
  {
    private UInt64 seqNum;
    private KVRequest req;

    public RequestMessage(UInt64 i_seqNum, KVRequest i_req)
    {
      seqNum = i_seqNum;
      req = i_req;
    }

    public UInt64 SeqNum { get { return seqNum; } }
    public KVRequest Request { get { return req; } }

    public byte[] Encode()
    {
      using (var memStream = new MemoryStream())
      {
        using (var requestMemStream = new MemoryStream())
        {
          req.Write(requestMemStream);
          byte[] encodedRequest = requestMemStream.ToArray();

          IoEncoder.WriteUInt64(memStream, 0);                                       // 0 means "this is a CMessage_Request"
          IoEncoder.WriteUInt64(memStream, seqNum);                                  // sequence number
          IoEncoder.WriteUInt64(memStream, (UInt64)encodedRequest.Length);           // size of CAppRequest
          IoEncoder.WriteBytes(memStream, encodedRequest, 0, (UInt64)encodedRequest.Length); // CAppRequest

          return memStream.ToArray();
        }
      }
    }
  }

  public class ReplyMessage
  {
    private UInt64 seqNum;
    private KVReply reply;

    private ReplyMessage(UInt64 i_seqNum, KVReply i_reply)
    {
      seqNum = i_seqNum;
      reply = i_reply;
    }

    public UInt64 SeqNum { get { return seqNum;  } }
    public KVReply Reply { get { return reply; } }
    
    public static ReplyMessage Decode(byte[] bytes)
    {
      if (bytes.Length < 24) {
        Console.Error.WriteLine("Got reply with invalid length {0}", bytes.Length);
        return null;
      }

      UInt64 messageType = IoEncoder.ExtractUInt64(bytes, 0);
      if (messageType != 6) {
        Console.Error.WriteLine("ERROR - Got message that wasn't a reply");
        return null;
      }

      UInt64 seqNum = IoEncoder.ExtractUInt64(bytes, 8);
      UInt64 replyLength = IoEncoder.ExtractUInt64(bytes, 16);
      if (replyLength + 24 != (UInt64)bytes.Length) {
        Console.Error.WriteLine("ERROR - Got reply with invalid encoded length ({0} instead of {1})",
                                replyLength, bytes.Length - 24);
        return null;
      }

      KVReply reply = KVReply.Extract(bytes, 24);
      return new ReplyMessage(seqNum, reply);
    }
  }

  public class HiResTimer
  {
    private static Stopwatch _stopWatch = null;
    public static long Ticks
    {
      get
      {
        return _stopWatch.ElapsedTicks;
      }
    }
    public static void Initialize()
    {
      _stopWatch = Stopwatch.StartNew();
    }
  }

  public class ThreadParams
  {
    public Params ps;
    public ulong id;

    public ThreadParams(ulong i_id, Params i_ps)
    {
      id = i_id;
      ps = i_ps;
    }
  }

  public class Client
  {
    public int id;
    public Params ps;
    public IoScheduler scheduler;

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
      scheduler = new IoScheduler(myEndpoint, true /* only client */, false /* verbose */);
      scheduler.Start();
      SeqNumManager seqNumManager = new SeqNumManager(myEndpoint.Port, ps.seqNumReservationSize);

      Thread.Sleep(3000);

      Random rng = new Random();

      // Create connections to all endpoints, so that if any of them
      // sends a reply we can receive it.  Since we're in "only
      // client" mode, we aren't listening on any port so we have to
      // rely on outgoing connections for all communication.

      foreach (var serverEp in ps.serverEps)
      {
        scheduler.Connect(serverEp);
      }

      // Start by guessing that the primary is server 0.  If it's not, we'll
      // time out and rotate to the proper server.

      int serverIdx = 0;

      while (true)
      {
        UInt64 seqNum = seqNumManager.Next;
        KVRequest req = GetRandomRequest(rng, ps);
        RequestMessage msg = new RequestMessage(seqNum, req);

        if (ps.verbose) {
          Console.WriteLine("Client {0}: Sending a request with sequence number {1} to {2}",
                            id, seqNum, ps.serverEps[serverIdx]);
        }

        var startTime = HiResTimer.Ticks;
        scheduler.SendPacket(ps.serverEps[serverIdx], msg.Encode());

        // Wait for the reply
        var receivedReply = false;
        while (!receivedReply)
        {
          bool ok;
          bool timedOut;
          IPEndPoint remote;
          byte[] bytes;
          scheduler.ReceivePacket(1000, out ok, out timedOut, out remote, out bytes);
          var endTime = HiResTimer.Ticks;

          if (timedOut) {
            serverIdx = (serverIdx + 1) % ps.serverEps.Count();
            Console.WriteLine("#timeout; rotating to server {0}", serverIdx);
            break;
          }
          if (!ok) {
            Console.WriteLine("Unrecoverable networking failure");
            return;
          }
          
          ReplyMessage reply = ReplyMessage.Decode(bytes);
          if (reply != null && reply.SeqNum == seqNum)
          {
            receivedReply = true;
            if (ps.verbose) {
              Console.Out.WriteLine("Received reply of type {0}", reply.Reply.ReplyType);
              if (reply.Reply is KVGetFoundReply gfr) {
                Console.Out.WriteLine("Value obtained for get was {0}", gfr.Val);
              }
            }
            // Report time in milliseconds, since that's what the Python script appears to expect
            Console.Out.WriteLine("#req{0} {1} {2} {3}",
                                  seqNum,
                                  (ulong)(startTime * 1000.0 / Stopwatch.Frequency),
                                  (ulong)(endTime * 1000.0 / Stopwatch.Frequency),
                                  id);
          }
        }
      }
    }
  }
}
