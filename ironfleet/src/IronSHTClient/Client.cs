using IronfleetCommon;
using IronfleetIoFramework;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Threading;

namespace IronSHTClient
{
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
    public byte[] myPublicKey;
    public ulong key;

    public GetRequestMessage(ulong seqNum, byte[] myPublicKey, ulong key) : base(0)
    {
      this.seqNum = seqNum;
      this.myPublicKey = myPublicKey;
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
        this.EncodeBytes(memStream, myPublicKey); // field two in CSingleMessage  
        this.EncodeUlong(memStream, (ulong)0); // case for GetRequest
        this.EncodeUlong(memStream, key); // field one in GetRequest
                
        return memStream.ToArray();
      }
    }
  }

  public class SetRequestMessage : MessageBase
  {
    public ulong seqNum;
    public byte[] myPublicKey;
    public ulong key;
    public ulong sizeValue;
    public Random rnd;

    public SetRequestMessage(ulong seqNum, byte[] myPublicKey, ulong key, ulong sizeValue) : base(0)
    {
      this.seqNum = seqNum;
      this.myPublicKey = myPublicKey;
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
        this.EncodeBytes(memStream, this.myPublicKey); // field two in CSingleMessage  
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
    public byte[] myPublicKey;
    public ulong k_lo, k_hi;
    public byte[] recipient;

    public ShardRequestMessage(ulong seqNum, byte[] myPublicKey, ulong k_lo, ulong k_hi, byte[] recipient) : base(0)
    {
      this.seqNum = seqNum;
      this.myPublicKey = myPublicKey;
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
        this.EncodeBytes(memStream, this.myPublicKey); // field two in CSingleMessage  
                
        this.EncodeUlong(memStream, (ulong)4); // case for ShardRequest

        // encode a KeyRange
        this.EncodeUlong(memStream, (ulong)0); // case for KeyPlus(k:Key)
        this.EncodeUlong(memStream, (ulong)k_lo); // klo
        this.EncodeUlong(memStream, (ulong)0); // case for KeyPlus(k:Key)
        this.EncodeUlong(memStream, (ulong)k_hi); // khi

        // encode the recipient
        this.EncodeBytes(memStream, this.recipient);

        return memStream.ToArray();
      }
    }
  }

  public class AckMessage : MessageBase
  {
    public byte[] Value { get; set; }
    public ulong seqNum;

    public AckMessage(ulong seqNum) : base(0)
    {
      this.seqNum = seqNum;
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
    public ServiceIdentity serviceIdentity;

    private Client(int i_id, Params i_ps, ServiceIdentity i_serviceIdentity)
    {
      id = i_id;
      ps = i_ps;
      serviceIdentity = i_serviceIdentity;
    }

    static public IEnumerable<Thread> StartSetupThreads(Params ps, ServiceIdentity serviceIdentity)
    {
      if (ps.NumThreads < 0)
      {
        throw new ArgumentException("count is less than 1", "count");
      }

      for (int i = 0; i < ps.NumSetupThreads; ++i)
      {
        var c = new Client(i, ps, serviceIdentity);
        Thread t = new Thread(c.Setup);
        t.Start();
        yield return t;
      }
    }

    static public IEnumerable<Thread> StartExperimentThreads(Params ps, ServiceIdentity serviceIdentity)
    {
      if (ps.NumThreads < 0)
      {
        throw new ArgumentException("count is less than 1", "count");
      }

      for (int i = 0; i < ps.NumThreads; ++i)
      {
        var c = new Client(i, ps, serviceIdentity);
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
      scheduler = IoScheduler.CreateClient(serviceIdentity.Servers, ps.Verbose);
      byte[] myPublicKey = IoScheduler.GetCertificatePublicKey(scheduler.MyCert);
            
      int serverIdx = 0;
      ulong seqNum = 0;
      ulong requestKey;

      for (requestKey = 0; requestKey < (ulong)ps.NumKeys; ++requestKey)
      {
        seqNum++;
        var msg = new SetRequestMessage(seqNum, myPublicKey, requestKey, (ulong)ps.ValueSize);

        if (ps.Verbose) {
          Console.WriteLine("Sending set request message with seq {0}, key {1} to server {2}", seqNum, requestKey, serverIdx);
        }
        this.Send(msg, serviceIdentity.Servers[serverIdx].PublicKey);
                
        // Wait for the reply
        var receivedReply = false;
        while (!receivedReply)
        {
          byte[] bytes = Receive();
          var endTime = HiResTimer.Ticks;
          if (bytes == null) {
            //serverIdx = (serverIdx + 1) % serviceIdentity.Servers.Count();
            Console.WriteLine("#timeout; retrying {0}", serverIdx);
            this.Send(msg, serviceIdentity.Servers[serverIdx].PublicKey);
            continue;
          }
          //Trace("Got the following reply:" + ByteArrayToString(bytes));
          //Console.Out.WriteLine("Got packet length: " + bytes.Length);
          if (bytes.Length == 16)
          {
            //Ignore acks
            if (ps.Verbose) {
              Console.WriteLine("Received ack");
            }
          }
          else if (bytes.Length >= 48) 
          {
            var replySeqNum = ExtractBE64(bytes, offset: 8);
            if (ps.Verbose) {
              Console.WriteLine("Reply sequence number : {0}", replySeqNum);
            }

            var ack_msg = new AckMessage(replySeqNum);

            if (ps.Verbose) {
              Console.Out.WriteLine("Client {0}: Sending an ack with sequence number {1} to {2}",
                                    id, replySeqNum, serviceIdentity.Servers[serverIdx]);
            }
            this.Send(ack_msg, serviceIdentity.Servers[serverIdx].PublicKey);

            int publicKeyLength = Convert.ToInt32(ExtractBE64(bytes, offset: 16));
            if (bytes.Length < publicKeyLength + 40) {
              Console.WriteLine("ERROR - Received too-short message (size {0} not long enough for public key of length {1})",
                                bytes.Length, publicKeyLength);
            }
            else {
              var replyKey = ExtractBE64(bytes, offset: 32 + publicKeyLength);
              // Need to send an ack
              if (ps.Verbose) {
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
    }

    private void ReceiveReply(int serverIdx, byte[] myPublicKey, ulong requestKey, bool receiveOnlyAcks)
    {
      var receivedReply = false;
      while (!receivedReply)
      {
        byte[] bytes = Receive();
        if (bytes == null) {
          Console.WriteLine("#timeout; retrying {0}", serverIdx);
          continue;
        }

        if (bytes.Length == 16)
        {
          var replySeqNum = ExtractBE64(bytes, offset: 8);
          if (ps.Verbose) {
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
          var ack_msg = new AckMessage(replySeqNum);
          this.Send(ack_msg, serviceIdentity.Servers[serverIdx].PublicKey);

          int publicKeyLength = Convert.ToInt32(ExtractBE64(bytes, offset: 16));
          if (bytes.Length < publicKeyLength + 40) {
            Console.WriteLine("ERROR - Received too-short message (size {0} not long enough for public key of length {1})",
                              bytes.Length, publicKeyLength);
          }
          else {
            var cmessage_case = ExtractBE64(bytes, offset: 24 + publicKeyLength);
            if (ps.Verbose) {
              Console.WriteLine("Received Message Case {0}", cmessage_case);
            }

            var replyKey = ExtractBE64(bytes, offset: 32 + publicKeyLength);
            if (ps.Verbose) {
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
    }

    public void Experiment()
    {
      ulong requestKey = 150;
      int serverIdx = 0;
            
      scheduler = IoScheduler.CreateClient(serviceIdentity.Servers, ps.Verbose);

      byte[] myPublicKey = IoScheduler.GetCertificatePublicKey(scheduler.MyCert);
      ulong seqNum = 0;
            
      // Test the functionality of the Sharding
      if (ps.Workload == 'f')
      {
        ulong k_lo = 100;
        ulong k_hi = 200;
        var recipient = serviceIdentity.Servers[(serverIdx + 1) % serviceIdentity.Servers.Count()];

        seqNum++;
        var msg = new GetRequestMessage(seqNum, myPublicKey, requestKey);
        this.Send(msg, serviceIdentity.Servers[serverIdx].PublicKey);
        ReceiveReply(serverIdx, myPublicKey, requestKey, false);

        seqNum++;
        Console.WriteLine("Sending a Shard request with a sequence number {0}", seqNum);
        var shardMessage = new ShardRequestMessage(seqNum, myPublicKey, k_lo, k_hi, recipient.PublicKey);
        this.Send(shardMessage, serviceIdentity.Servers[serverIdx].PublicKey);
        ReceiveReply(serverIdx, myPublicKey, requestKey, true);

        Thread.Sleep(5000);

        Console.WriteLine("Sending a GetRequest after a Shard, expect a redirect");

        seqNum++;
        msg = new GetRequestMessage(seqNum, myPublicKey, requestKey);
        this.Send(msg, serviceIdentity.Servers[(serverIdx + 0) % serviceIdentity.Servers.Count()].PublicKey);
        ReceiveReply(serverIdx, myPublicKey, requestKey, false);

        Thread.Sleep(5000);

        Console.WriteLine("Sending a GetRequest after a Shard to the second host, expect a reply");
        seqNum++;
        msg = new GetRequestMessage(seqNum, myPublicKey, requestKey);
        this.Send(msg, serviceIdentity.Servers[(serverIdx + 1) % serviceIdentity.Servers.Count()].PublicKey);
        ReceiveReply(serverIdx, myPublicKey, requestKey, false);
                
        return;
      }

      // Run an actual workload
      while (true)
      {
        seqNum++;
        var receivedReply = false;
        requestKey = seqNum % (ulong)ps.NumKeys;
                               
        MessageBase msg;
        if (ps.Workload == 'g') 
        {
          msg = new GetRequestMessage(seqNum, myPublicKey, requestKey);
        }
        else
        {
          msg = new SetRequestMessage(seqNum, myPublicKey, requestKey, (ulong)ps.ValueSize);
        }

        var startTime = HiResTimer.Ticks;
        this.Send(msg, serviceIdentity.Servers[serverIdx].PublicKey);
        
        // Wait for the reply
                
        while (!receivedReply)
        {
          byte[] bytes = Receive();
          if (bytes == null) {
            //serverIdx = (serverIdx + 1) % serviceIdentity.Servers.Count();
            //Console.WriteLine("#timeout; rotating to server {0}", serverIdx);
            Console.WriteLine("#timeout; retrying {0}", serverIdx);
            this.Send(msg, serviceIdentity.Servers[serverIdx].PublicKey);
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
            if (ps.Verbose)
            {
              Console.WriteLine("Reply sequence number : {0}", replySeqNum);
              Console.WriteLine("Client {0}: Sending an ack with sequence number {1} to {2}",
                                id, replySeqNum, serviceIdentity.Servers[serverIdx]);
            }
            if (seqNum % 100 == 0)
            {
              var ack_msg = new AckMessage(replySeqNum);
              this.Send(ack_msg, serviceIdentity.Servers[serverIdx].PublicKey);
            }

            int publicKeyLength = Convert.ToInt32(ExtractBE64(bytes, offset: 16));
            if (bytes.Length < publicKeyLength + 40)
            {
              Console.WriteLine("ERROR - Received too-short message (size {0} not long enough for public key of length {1})",
                                bytes.Length, publicKeyLength);
            }
            else
            {
              var replyKey = ExtractBE64(bytes, offset: 32 + publicKeyLength);
              // Need to send an ack
              if (ps.Verbose)
              {
                Console.WriteLine("Request key : {0}", requestKey);
                Console.WriteLine("Reply key : {0}", replyKey);
                Console.WriteLine("Got packet length: {0}", bytes.Length);
              }

              // key is the same as the sequence number
              if (replyKey == requestKey)
              {
                receivedReply = true;
                Console.WriteLine("#req {0} {1} {2}",
                                  id,
                                  seqNum,
                                  HiResTimer.TicksToMilliseconds(endTime - startTime));
              }
            }
          }
          else {
            Console.WriteLine("Received packet of unexpected length {0}", bytes.Length);
          }
        }
      }
    }

    private void Send(MessageBase msg, byte[] remote)
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
      byte[] remote;
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
