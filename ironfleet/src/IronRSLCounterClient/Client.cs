using IronfleetCommon;
using IronfleetIoFramework;
using System;
using System.Collections.Generic;
using System.IO;
using System.Net;
using System.Threading;
using System.Diagnostics;
using System.Linq;

namespace IronRSLCounterClient
{
  public class IncrementRequestMessage
  {
    public UInt64 seqNum;

    public IncrementRequestMessage(UInt64 i_seqNum)
    {
      seqNum = i_seqNum;
    }

    public byte[] Encode()
    {
      using (var memStream = new MemoryStream())
      {
        IoEncoder.WriteUInt64(memStream, 0);             // case for CMessage_Request
        IoEncoder.WriteUInt64(memStream, seqNum);        // sequence number field in CMessage_Request
        IoEncoder.WriteUInt64(memStream, (UInt64)8);     // size of CAppRequest
        IoEncoder.WriteUInt64(memStream, 0);             // request type (0 = increment)

        return memStream.ToArray();
      }
    }
  }

  public class ReplyMessage
  {
    public UInt64 seqNum;
    public UInt64 counterValue;

    public ReplyMessage(UInt64 i_seqNum, UInt64 i_counterValue)
    {
      seqNum = i_seqNum;
      counterValue = i_counterValue;
    }
    
    public static ReplyMessage Decode(byte[] bytes)
    {
      if (bytes.Length != 32) {
        Console.Error.WriteLine("Got invalid-length reply");
        return null;
      }

      UInt64 messageType = IoEncoder.ExtractUInt64(bytes, 0);
      if (messageType != 6) {
        Console.Error.WriteLine("ERROR - Got message that wasn't a reply");
        return null;
      }

      UInt64 seqNum = IoEncoder.ExtractUInt64(bytes, 8);
      UInt64 replyLength = IoEncoder.ExtractUInt64(bytes, 16);
      if (replyLength != 8) {
        Console.Error.WriteLine("ERROR - Got reply of invalid length");
        return null;
      }

      UInt64 counterValue = IoEncoder.ExtractUInt64(bytes, 24);
      return new ReplyMessage(seqNum, counterValue);
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

    private void Run()
    {
      IPEndPoint myEndpoint = new IPEndPoint(IPAddress.Parse("127.0.0.1"), ps.clientPort + (int)id);
      scheduler = new IoScheduler(myEndpoint, true /* only client */, false /* verbose */);
      scheduler.Start();
      SeqNumManager seqNumManager = new SeqNumManager(myEndpoint.Port, ps.seqNumReservationSize);

      Thread.Sleep(3000);

      // Create connections to all endpoints, so that if any of them
      // sends a reply we can receive it.  Since we're in "only
      // client" mode, we aren't listening on any port so we have to
      // rely on outgoing connections for all communication.

      foreach (var serverEp in ps.serverEps)
      {
        scheduler.Connect(serverEp);
      }

      int serverIdx = 0;

      while (true)
      {
        UInt64 seqNum = seqNumManager.Next;
        var msg = new IncrementRequestMessage(seqNum);

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
          if (reply != null && reply.seqNum == seqNum)
          {
            receivedReply = true;
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
