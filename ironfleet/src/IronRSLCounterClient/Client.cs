using IronfleetIoFramework;
using System;
using System.Collections.Generic;
using System.IO;
using System.Net;
using System.Threading;
using System.Diagnostics;
using System.Linq;

namespace IronRSLClient
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

  public struct Param
  {
    public ulong id;
    public int port_num;
    public ulong initial_seq_no;
  }

  public class Client
  {
    public IoScheduler scheduler;
    public static List<IPEndPoint> endpoints;
    public static IPAddress my_addr;
    public static bool DEBUG = false;

    public static void StartThread(object p)
    {
      Thread.Sleep(3000);
      var c = new Client();
      c.Main(((Param)p).id, ((Param)p).port_num, ((Param)p).initial_seq_no);
    }

    static public IEnumerable<Thread> StartThreads<T>(ulong num_threads, int port_num, ulong initial_seq_no)
    {
      if (num_threads < 0)
      {
        throw new ArgumentException("number of threads is less than 1", "num_threads");
      }

      for (ulong i = 0; i < num_threads; ++i)
      {
        var t = new Thread(StartThread);
        var p = new Param { id = i, port_num = port_num, initial_seq_no = initial_seq_no };
        t.Start(p);
        yield return t;
      }
    }

    //private static long num_reqs = 0;

    public static void Trace(string str)
    {
      if (DEBUG)
      {
        Console.Out.WriteLine(str);
      }    
    }
  
    public string ByteArrayToString(byte[] ba)
    {
      string hex = BitConverter.ToString(ba);
      return hex.Replace("-", "");
    }

    protected void Main(ulong id, int port_num, ulong initial_seq_no)
    {
      IPEndPoint myEndpoint = new IPEndPoint(my_addr, port_num+(int)id);
      scheduler = new IoScheduler(myEndpoint, true /* only client */, false /* verbose */);
      scheduler.Start();

      // Create connections to all endpoints, so that if any of them
      // sends a reply we can receive it.  Since we're in "only
      // client" mode, we aren't listening on any port so we have to
      // rely on outgoing connections for all communication.

      foreach (var remote in Client.endpoints)
      {
        scheduler.Connect(remote);
      }

      int serverIdx = 0;

      for (ulong seq_no = initial_seq_no; true; ++seq_no)
      {
        var msg = new IncrementRequestMessage(seq_no);

        Trace("Client " + id.ToString() + ": Sending a request with a sequence number " + seq_no + " to " + Client.endpoints[serverIdx].ToString());

        var start_time = HiResTimer.Ticks;
        scheduler.SendPacket(Client.endpoints[serverIdx], msg.Encode());
        //foreach (var remote in ClientBase.endpoints)
        //{
        //    this.Send(msg, remote);
        //}

        // Wait for the reply
        var received_reply = false;
        while (!received_reply)
        {
          bool ok;
          bool timedOut;
          IPEndPoint remote;
          byte[] bytes;
          scheduler.ReceivePacket(1000, out ok, out timedOut, out remote, out bytes);

          if (timedOut) {
            serverIdx = (serverIdx + 1) % Client.endpoints.Count();
            Console.WriteLine("#timeout; rotating to server {0}", serverIdx);
            break;
          }
          if (!ok) {
            Console.WriteLine("Unrecoverable networking failure");
            return;
          }
          
          var end_time = HiResTimer.Ticks;
          Trace("Got the following reply:" + ByteArrayToString(bytes));
          ReplyMessage reply = ReplyMessage.Decode(bytes);
          if (reply != null && reply.seqNum == seq_no)
          {
            received_reply = true;
            // Report time in milliseconds, since that's what the Python script appears to expect
            Console.Out.WriteLine(string.Format("#req{0} {1} {2} {3}", seq_no, (ulong)(start_time * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3)), (ulong)(end_time * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3)), id));
          }
        }
      }
    }
  }
}
