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

namespace IronRSLClient
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

  public struct Param
  {
    public ulong id;
    public int port_num;
    public ulong initial_seq_no;
    public double set_fraction;
    public double delete_fraction;
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
      c.Main(((Param)p).id, ((Param)p).port_num, ((Param)p).initial_seq_no, ((Param)p).set_fraction, ((Param)p).delete_fraction);
    }

    static public IEnumerable<Thread> StartThreads<T>(ulong num_threads, int port_num, ulong initial_seq_no, double set_fraction, double delete_fraction)
    {
      if (num_threads < 0)
      {
        throw new ArgumentException("number of threads is less than 1", "num_threads");
      }

      for (ulong i = 0; i < num_threads; ++i)
      {
        var t = new Thread(StartThread);
        var p = new Param { id = i, port_num = port_num, initial_seq_no = initial_seq_no, set_fraction = set_fraction, delete_fraction = delete_fraction };
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

    private static KVRequest GetRandomRequest(Random rng, double set_fraction, double delete_fraction)
    {
      int keySelector = rng.Next(26);
      char k = (char)('a' + keySelector);
      StringBuilder keyBuilder = new StringBuilder();
      keyBuilder.Append(k);
      keyBuilder.Append(k);
      keyBuilder.Append(k);
      string key = keyBuilder.ToString();
      
      int reqTypeSelector = rng.Next();
      if (reqTypeSelector < set_fraction * Int32.MaxValue) {
        char v = (char)('A' + keySelector);
        StringBuilder valBuilder = new StringBuilder();
        valBuilder.Append(v);
        valBuilder.Append(v);
        valBuilder.Append(v);
        valBuilder.Append(v);
        valBuilder.Append(rng.Next(100000));
        string val = valBuilder.ToString();
        //        Console.WriteLine("Submitting set request for {0} => {1}", key, val);
        return new KVSetRequest(key, val);
      }
      else if (reqTypeSelector < (set_fraction + delete_fraction) * Int32.MaxValue) {
        //        Console.WriteLine("Submitting delete request for {0}", key);
        return new KVDeleteRequest(key);
      }
      else {
        //        Console.WriteLine("Submitting get request for {0}", key);
        return new KVGetRequest(key);
      }
    }

    protected void Main(ulong id, int port_num, ulong initial_seq_no, double set_fraction, double delete_fraction)
    {
      IPEndPoint myEndpoint = new IPEndPoint(my_addr, port_num+(int)id);
      scheduler = new IoScheduler(myEndpoint, true /* only client */, false /* verbose */);
      scheduler.Start();

      Random rng = new Random();

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
        KVRequest req = GetRandomRequest(rng, set_fraction, delete_fraction);
        RequestMessage msg = new RequestMessage(seq_no, req);

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
          if (reply != null && reply.SeqNum == seq_no)
          {
            received_reply = true;
            /*
            Console.Out.WriteLine("Received reply of type {0}", reply.Reply.ReplyType);
            if (reply.Reply is KVGetFoundReply gfr) {
              Console.Out.WriteLine("Value obtained for get was {0}", gfr.Val);
            }
            */
            // Report time in milliseconds, since that's what the Python script appears to expect
            Console.Out.WriteLine(string.Format("#req{0} {1} {2} {3}", seq_no, (ulong)(start_time * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3)), (ulong)(end_time * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3)), id));
          }
        }
      }
    }
  }
}
