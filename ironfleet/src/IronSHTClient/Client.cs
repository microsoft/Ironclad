using IronfleetIoFramework;
using IronfleetCommon;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Net;
using System.Threading;

namespace IronSHTClient
{
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

  public abstract class MessageBase
  {
    public ulong CaseId { get; private set; }

    protected MessageBase(ulong caseId)
    {
      this.CaseId = caseId;
    }

    public abstract byte[] ToBigEndianByteArray();

    public byte[] ToByteArray()
    {
      return this.ToBigEndianByteArray();
    }

    protected void EncodeUlong(MemoryStream memStream, ulong value)
    {
      if (null == memStream)
      {
        throw new ArgumentNullException("memStream");
      }

      var bytes = BitConverter.GetBytes(value);
      if (BitConverter.IsLittleEndian)
      {
        Array.Reverse(bytes);
      }
      memStream.Write(bytes, 0, bytes.Length);
    }

    protected void EncodeBool(MemoryStream memStream, bool value)
    {
      this.EncodeUlong(memStream, value ? 1UL : 0);
    }

    protected void EncodeBytes(MemoryStream memStream, byte[] value)
    {
      if (null == value)
      {
        throw new ArgumentNullException("value");
      }

      this.EncodeUlong(memStream, (ulong)value.Length);
      memStream.Write(value, 0, value.Length);
    }

    protected void EncodeHeader(MemoryStream memStream)
    {
      this.EncodeUlong(memStream, CaseId);
    }
  }

  public class GetRequestMessage : MessageBase
  {
    public byte[] Value { get; set; }
    public ulong seqNum;
    public ulong myaddr;
    public ulong key;

    public GetRequestMessage(ulong seqNum, ulong myaddr, ulong key) : base(0)
    {
      this.seqNum = seqNum;
      this.myaddr = myaddr;
      this.key = key;    
    }

    public override byte[] ToBigEndianByteArray()
    {
      return this.Encode();
    }

    public ulong GetSeqNum()
    {
      return seqNum;
    }

    private byte[] Encode(bool retrans = false)
    {
      using (var memStream = new MemoryStream())
      {
        this.EncodeUlong(memStream, (ulong)0); // case for CSingleMessage
        this.EncodeUlong(memStream, (ulong)seqNum); // field one in CSingleMessage
        this.EncodeUlong(memStream, (ulong)this.myaddr); // field two in CSingleMessage  
        this.EncodeUlong(memStream, (ulong)0); // case for GetRequest
        this.EncodeUlong(memStream, key); // field one in GetRequest
                
        return memStream.ToArray();
      }
    }
  }

  public class SetRequestMessage : MessageBase
  {
    public ulong seqNum;
    public ulong myaddr;
    public ulong key;
    public ulong sizeValue;
    public Random rnd;

    public SetRequestMessage(ulong seqNum, ulong myaddr, ulong key, ulong sizeValue) : base(0)
    {
      this.seqNum = seqNum;
      this.myaddr = myaddr;
      this.key = key;
      this.sizeValue = sizeValue;
      rnd = new Random();
    }

    public override byte[] ToBigEndianByteArray()
    {
      return this.Encode();
    }

    public ulong GetSeqNum()
    {
      return seqNum;
    }

    private byte[] Encode(bool retrans = false)
    {
      using (var memStream = new MemoryStream())
      {
        byte[] value = new byte[sizeValue];
                         
        rnd.NextBytes(value);

        this.EncodeUlong(memStream, (ulong)0); // case for CSingleMessage
        this.EncodeUlong(memStream, (ulong)seqNum); // field one in CSingleMessage
        this.EncodeUlong(memStream, (ulong)this.myaddr); // field two in CSingleMessage  
        this.EncodeUlong(memStream, (ulong)1); // case for SetRequest
        this.EncodeUlong(memStream, key); // field one in SetRequest
        this.EncodeUlong(memStream, (ulong)0); // case for OptionalValue
        this.EncodeBytes(memStream, value); // field two in SetRequest
        return memStream.ToArray();
      }
    }
  }

  public class ShardRequestMessage : MessageBase
  {
    public ulong seqNum;
    public ulong myaddr;
    public ulong k_lo, k_hi;
    public ulong recipient;

    public ShardRequestMessage(ulong seqNum, ulong myaddr, ulong k_lo, ulong k_hi, ulong recipient) : base(0)
    {
      this.seqNum = seqNum;
      this.myaddr = myaddr;
      this.k_lo = k_lo;
      this.k_hi = k_hi;
      this.recipient = recipient;
    }

    public override byte[] ToBigEndianByteArray()
    {
      return this.Encode();
    }

    public ulong GetSeqNum()
    {
      return seqNum;
    }

    private byte[] Encode(bool retrans = false)
    {
      using (var memStream = new MemoryStream())
      {
        this.EncodeUlong(memStream, (ulong)0); // case for CSingleMessage
        this.EncodeUlong(memStream, (ulong)seqNum); // field one in CSingleMessage
        this.EncodeUlong(memStream, (ulong)this.myaddr); // field two in CSingleMessage  
                
        this.EncodeUlong(memStream, (ulong)4); // case for ShardRequest

        // encode a KeyRange
        this.EncodeUlong(memStream, (ulong)0); // case for KeyPlus(k:Key)
        this.EncodeUlong(memStream, (ulong)k_lo); // klo
        this.EncodeUlong(memStream, (ulong)0); // case for KeyPlus(k:Key)
        this.EncodeUlong(memStream, (ulong)k_hi); // khi

        // encode the recipient
        this.EncodeUlong(memStream, this.recipient);

        return memStream.ToArray();
      }
    }
  }

  public class AckMessage : MessageBase
  {
    public byte[] Value { get; set; }
    public ulong seqNum;
    public ulong myaddr;

    public AckMessage(ulong seqNum, ulong myaddr) : base(0)
    {
      this.seqNum = seqNum;
      this.myaddr = myaddr;
    }

    public override byte[] ToBigEndianByteArray()
    {
      return this.Encode();
    }

    public ulong GetSeqNum()
    {
      return seqNum;
    }

    private byte[] Encode(bool retrans = false)
    {
      using (var memStream = new MemoryStream())
      {
        this.EncodeUlong(memStream, (ulong)1); // case for CAck
        this.EncodeUlong(memStream, (ulong)seqNum); // field one in CSingleMessage
        return memStream.ToArray();
      }
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

    static public IEnumerable<Thread> StartSetupThreads(Params ps)
    {
      if (ps.numThreads < 0)
      {
        throw new ArgumentException("count is less than 1", "count");
      }

      for (int i = 0; i < ps.numSetupThreads; ++i)
      {
        var c = new Client(i, ps);
        Thread t = new Thread(c.Setup);
        t.Start();
        yield return t;
      }
    }

    static public IEnumerable<Thread> StartExperimentThreads(Params ps)
    {
      if (ps.numThreads < 0)
      {
        throw new ArgumentException("count is less than 1", "count");
      }

      for (int i = 0; i < ps.numThreads; ++i)
      {
        var c = new Client(i, ps);
        Thread t = new Thread(c.Experiment);
        t.Start();
        yield return t;
      }
    }

    public string ByteArrayToString(byte[] ba)
    {
      string hex = BitConverter.ToString(ba);
      return hex.Replace("-", "");
    }

    public void Setup()
    {
      ulong seqNum = 0;

      IPEndPoint myEndpoint = new IPEndPoint(ps.clientEp.Address, ps.clientEp.Port + (int)id);
      scheduler = new IoScheduler(myEndpoint, false /* only client */, false /* verbose */);
      scheduler.Start();

      ulong myaddr = EncodeIpPort(myEndpoint);
            
      int serverIdx = 0;

      while (seqNum < (ulong)ps.numKeys)
      {
        var requestKey = seqNum % (ulong)ps.numKeys;

        seqNum++;
        var msg = new SetRequestMessage(seqNum, myaddr, requestKey, (ulong)ps.valueSize);
                
        this.Send(msg, ps.serverEps[serverIdx]);
                
        // Wait for the reply
        var receivedReply = false;
        while (!receivedReply)
        {
          byte[] bytes = Receive();
          if (bytes == null) {
            //serverIdx = (serverIdx + 1) % ps.serverEps.Count();
            Console.WriteLine("#timeout; retrying {0}", serverIdx);
            continue;
          }
          var endTime = HiResTimer.Ticks;
          //Trace("Got the following reply:" + ByteArrayToString(bytes));
          //Console.Out.WriteLine("Got packet length: " + bytes.Length);
          if (bytes.Length == 16)
          {
            //Ignore acks
          }
          else if (bytes.Length >= 48) 
          {
            var replySeqNum = ExtractBE64(bytes, offset: 8);
            if (ps.verbose) {
              Console.WriteLine("Reply sequence number : {0}", replySeqNum);
            }

            var ack_msg = new AckMessage(replySeqNum, myaddr);

            if (ps.verbose) {
              Console.Out.WriteLine("Client {0}: Sending an ack with sequence number {1} to {2}",
                                    id, replySeqNum, ps.serverEps[serverIdx]);
            }
            this.Send(ack_msg, ps.serverEps[serverIdx]);

            var replyKey = ExtractBE64(bytes, offset: 32);
            // Need to send an ack
            if (ps.verbose) {
              Console.WriteLine("Request key : {0}", requestKey);
              Console.WriteLine("Reply key : {0}", replyKey);
              Console.WriteLine("Got packet length: {0}", bytes.Length);
            }

            if (replyKey == requestKey)
            {
              receivedReply = true;
            }
          }
        }
      }
    }

    private void ReceiveReply(int serverIdx, ulong myaddr, ulong requestKey, bool receiveOnlyAcks)
    {
      var receivedReply = false;
      while (!receivedReply)
      {
        byte[] bytes;
        try
        {
          bytes = Receive();
        }
        catch (System.Net.Sockets.SocketException e)
        {
          Console.WriteLine(e.ToString());
          Console.WriteLine("#timeout; retrying {0}", serverIdx);
          continue;
        }

        if (bytes.Length == 16)
        {
          var replySeqNum = ExtractBE64(bytes, offset: 8);
          if (ps.verbose) {
            Console.WriteLine("Received an ack for sequence number {0}", replySeqNum);
          }
                    
          if (receiveOnlyAcks)
          {
            receivedReply = true;
          }
        }
        else if (bytes.Length >= 48)
        {
          var replySeqNum = ExtractBE64(bytes, offset: 8);
          var ack_msg = new AckMessage(replySeqNum, myaddr);
          this.Send(ack_msg, ps.serverEps[serverIdx]);

          var cmessage_case = ExtractBE64(bytes, offset: 24);
          if (ps.verbose) {
            Console.WriteLine("Received Message Case {0}", cmessage_case);
          }

          var replyKey = ExtractBE64(bytes, offset: 32);
          if (ps.verbose) {
            if (cmessage_case == 2) {
              Console.WriteLine("Received a reply with key {0}", replyKey);
            }
            else if (cmessage_case == 3) {
              Console.WriteLine("Received a redirect for key {0}", replyKey);
            }
          }

          if (replyKey == requestKey && cmessage_case == 2)
          {
            receivedReply = true;
          }
        }
      }
    }

    public void Experiment()
    {
      ulong requestKey = 150;
      int serverIdx = 0;
      UInt64 seqNum;
            
      IPEndPoint myEndpoint = new IPEndPoint(ps.clientEp.Address, ps.clientEp.Port + ps.numSetupThreads + (int)id);
      scheduler = new IoScheduler(myEndpoint, false /* only client */, false /* verbose */);
      scheduler.Start();
      SeqNumManager seqNumManager = new SeqNumManager(myEndpoint.Port, ps.seqNumReservationSize);

      ulong myaddr = EncodeIpPort(myEndpoint);
            
      // Test the functionality of the Sharding
      if (ps.workload == 'f')
      {
        ulong k_lo = 100;
        ulong k_hi = 200;
        var recipient = EncodeIpPort(ps.serverEps[(serverIdx + 1) % ps.serverEps.Count()]);

        seqNum = seqNumManager.Next;

        var msg = new GetRequestMessage(seqNum, myaddr, requestKey);
        this.Send(msg, ps.serverEps[serverIdx]);
        ReceiveReply(serverIdx, myaddr, requestKey, false);

        seqNum = seqNumManager.Next;

        Console.WriteLine("Sending a Shard request with a sequence number {0}", seqNum);
        var shardMessage = new ShardRequestMessage(seqNum, myaddr, k_lo, k_hi, recipient);
        this.Send(shardMessage, ps.serverEps[serverIdx]);
        ReceiveReply(serverIdx, myaddr, requestKey, true);

        Thread.Sleep(5000);

        Console.WriteLine("Sending a GetRequest after a Shard, expect a redirect");

        seqNum = seqNumManager.Next;
        msg = new GetRequestMessage(seqNum, myaddr, requestKey);
        this.Send(msg, ps.serverEps[(serverIdx + 0) % ps.serverEps.Count()]);
        ReceiveReply(serverIdx, myaddr, requestKey, false);

        Thread.Sleep(5000);

        Console.WriteLine("Sending a GetRequest after a Shard to the second host, expect a reply");
        seqNum = seqNumManager.Next;
        msg = new GetRequestMessage(seqNum, myaddr, requestKey);
        this.Send(msg, ps.serverEps[(serverIdx + 1) % ps.serverEps.Count()]);
        ReceiveReply(serverIdx, myaddr, requestKey, false);
                
        return;
      }

      // Run an actual workload
      while (true)
      {
        seqNum = seqNumManager.Next;
        var receivedReply = false;
        requestKey = seqNum % (ulong)ps.numKeys;
                               
        MessageBase msg;
        if (ps.workload == 'g') 
        {
          msg = new GetRequestMessage(seqNum, myaddr, requestKey);
        }
        else
        {
          msg = new SetRequestMessage(seqNum, myaddr, requestKey, (ulong)ps.valueSize);
        }
        
        var startTime = HiResTimer.Ticks;
        this.Send(msg, ps.serverEps[serverIdx]);
                
        // Wait for the reply
                
        while (!receivedReply)
        {
          byte[] bytes;
          try
          {
            bytes = Receive();
          }
          catch (System.Net.Sockets.SocketException)
          {
            //serverIdx = (serverIdx + 1) % ps.serverEps.Count();
            //Console.WriteLine("#timeout; rotating to server {0}", serverIdx);
            //Console.WriteLine(e.ToString());
            Console.WriteLine("#timeout; retrying {0}", serverIdx);
            continue;
          }
          var endTime = HiResTimer.Ticks;
                    
          if (bytes.Length == 16)
          {
            //Ignore acks
          }
          else if (bytes.Length >= 56) 
          {
            var replySeqNum = ExtractBE64(bytes, offset: 8);
            if (ps.verbose) {
              Console.WriteLine("Reply sequence number : {0}", replySeqNum);
              Console.WriteLine("Client {0}: Sending an ack with sequence number {1} to {2}",
                                id, replySeqNum, ps.serverEps[serverIdx]);
            }
            if (seqNum % 100 == 0)
            {
              var ack_msg = new AckMessage(replySeqNum, myaddr);
              this.Send(ack_msg, ps.serverEps[serverIdx]);
            }

            var replyKey = ExtractBE64(bytes, offset: 32);
            // Need to send an ack
            if (ps.verbose) {
              Console.WriteLine("Request key : {0}", requestKey);
              Console.WriteLine("Reply key : {0}", replyKey);
              Console.WriteLine("Got packet length: {0}", bytes.Length);
            }

            // key is the same as the sequence number
            if (replyKey == requestKey)
            {
              receivedReply = true;
              Console.WriteLine("#req{0} {1} {2} {3}",
                                seqNum,
                                (ulong)(startTime * 1000.0 / Stopwatch.Frequency),
                                (ulong)(endTime * 1000.0 / Stopwatch.Frequency),
                                id);
            }
          }
          else {
            Console.WriteLine("Received packet of unexpected length {0}", bytes.Length);
          }
        }
      }
    }

    private void Send(MessageBase msg, System.Net.IPEndPoint remote)
    {
      var a = msg.ToBigEndianByteArray();
      if (!scheduler.SendPacket(remote, a))
      {
        throw new InvalidOperationException("failed to send complete message.");
      }
    }

    private byte[] Receive()
    {
      bool ok;
      bool timedOut;
      IPEndPoint remote;
      byte[] buffer;
      scheduler.ReceivePacket(1000, out ok, out timedOut, out remote, out buffer);
      return buffer;
    }

    public ulong EncodeIpPort(IPEndPoint ep)
    {
      ushort port = (ushort)ep.Port;
      byte[] addrBytes = ep.Address.GetAddressBytes();
      uint addr = ExtractBE32(addrBytes, 0);

      MemoryStream str = new MemoryStream();
      ushort preamble = 0;
      var bytes = BitConverter.GetBytes(preamble);
      str.Write(bytes, 0, bytes.Length);
      bytes = BitConverter.GetBytes(addr);
      if (BitConverter.IsLittleEndian)
      {
        Array.Reverse(bytes);
      }
      str.Write(bytes, 0, bytes.Length);
      bytes = BitConverter.GetBytes(port);
      if (BitConverter.IsLittleEndian)
      {
        Array.Reverse(bytes);
      }
      str.Write(bytes, 0, bytes.Length);
      byte[] s = str.ToArray();
      Array.Reverse(s);
      return BitConverter.ToUInt64(s, 0);
    }

    public static UInt64 ExtractBE64(byte[] byteArray, int offset)
    {
      byte[] extractedBytes = byteArray.Skip(offset).Take(8).ToArray();
      Array.Reverse(extractedBytes);
      return BitConverter.ToUInt64(extractedBytes, 0);
    }

    public static UInt32 ExtractBE32(byte[] byteArray, int offset)
    {
      byte[] extractedBytes = byteArray.Skip(offset).Take(4).ToArray();
      Array.Reverse(extractedBytes);
      return BitConverter.ToUInt32(extractedBytes, 0);
    }
  }
}
