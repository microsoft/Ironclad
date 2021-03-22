namespace IronfleetTestDriver.IronSHT
{
    using System;
    using System.IO;
    using System.Net;
    using System.Threading;
    using System.Diagnostics;
    using System.Linq;

    /*
    public class HiResTimer 
    {
        private static DateTime _startTime;
        private static Stopwatch _stopWatch = null;
        public static DateTime UtcNow
        {       get
                {
                    if (_stopWatch == null)
                    {
                        Reset();
                    }
                    return _startTime.AddTicks(_stopWatch.Elapsed.Ticks);
                }
        }
        private static void Reset()
        {
            _startTime = DateTime.UtcNow;
            _stopWatch = Stopwatch.StartNew();
        }
    }
     */

    public class GetRequestMessage : MessageBase
    {
        public byte[] Value { get; set; }
        public ulong seqNum;
        public ulong myaddr;
        public ulong key;

        public GetRequestMessage(ulong seqNum, ulong myaddr, ulong key)
            : base(0)
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

        public SetRequestMessage(ulong seqNum, ulong myaddr, ulong key, ulong sizeValue)
            : base(0)
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

        public ShardRequestMessage(ulong seqNum, ulong myaddr, ulong k_lo, ulong k_hi, ulong recipient)
            : base(0)
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

        public AckMessage(ulong seqNum, ulong myaddr)
            : base(0)
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



    public class Client : ClientBase
    {
        public static bool DEBUG = false;

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

        protected override void Setup(int base_client_port, ulong id, ulong num_keys, ulong size_value)
        {
            ulong seq_num = 0;

            this.udpClient = new System.Net.Sockets.UdpClient(base_client_port+(int)id);
            this.udpClient.Client.ReceiveTimeout = 1000;
            ulong myaddr = MyAddress64();
            
            int serverIdx = 0;

            while (seq_num < num_keys)
            {
                var request_key = seq_num % num_keys;

                seq_num++;
                var msg = new SetRequestMessage(seq_num, myaddr, request_key, size_value);
                
                this.Send(msg, ClientBase.endpoints[serverIdx]);
                
                // Wait for the reply
                var received_reply = false;
                while (!received_reply)
                {
                    byte[] bytes;
                    try
                    {
                        bytes = Receive();
                    }
                    catch (System.Net.Sockets.SocketException e)
                    {
                        //serverIdx = (serverIdx + 1) % ClientBase.endpoints.Count();
                        Console.WriteLine("#timeout; retrying {0}", serverIdx);
                        Console.WriteLine(e.ToString());
                        continue;
                    }
                    var end_time = HiResTimer.Ticks;
                    //Trace("Got the following reply:" + ByteArrayToString(bytes));
                    //Console.Out.WriteLine("Got packet length: " + bytes.Length);
                    if (bytes.Length == 16)
                    {
                        //Ignore acks
                    }
                    else if (bytes.Length >= 48) 
                    {
                        var reply_seqno = ExtractBE64(bytes, offset: 8);
                        //Console.Out.WriteLine("Reply sequence number : " + reply_seqno);

                        var ack_msg = new AckMessage(reply_seqno, myaddr);

                        //Console.Out.WriteLine("Client " + id.ToString() + ": Sending an ack with a sequence number " + reply_seqno + " to " + ClientBase.endpoints[serverIdx].ToString());
                        this.Send(ack_msg, ClientBase.endpoints[serverIdx]);


                        var reply_key = ExtractBE64(bytes, offset: 32);
                        // Need to send an ack
                        //Console.Out.WriteLine("Request key : " + request_key);
                        //Console.Out.WriteLine("Reply key : " + reply_key);

                        //Console.Out.WriteLine("Got packet length: " + bytes.Length);
                        if (reply_key == request_key)
                        {
                            received_reply = true;
                            // Report time in milliseconds, since that's what the Python script appears to expect
                            //Console.Out.WriteLine(string.Format("#req{0} {1} {2} {3}", seq_num, (ulong)(start_time * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3)), (ulong)(end_time * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3)), id));
                        }
                    }
                }
            }

            this.udpClient.Close();
        }

        private void ReceiveReply(int serverIdx, ulong myaddr, ulong request_key, bool receive_only_acks)
        {
            var received_reply = false;
            while (!received_reply)
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
                    var reply_seqno = ExtractBE64(bytes, offset: 8);
                    Console.WriteLine("Received an ack for sequence number {0}", reply_seqno);
                    
                    if (receive_only_acks)
                    {
                        received_reply = true;
                    }
                }
                else if (bytes.Length >= 48)
                {
                    var reply_seqno = ExtractBE64(bytes, offset: 8);
                    var ack_msg = new AckMessage(reply_seqno, myaddr);
                    this.Send(ack_msg, ClientBase.endpoints[serverIdx]);

                    var cmessage_case = ExtractBE64(bytes, offset: 24);
                    Console.WriteLine("Received Message Case {0}", cmessage_case);

                    var reply_key = ExtractBE64(bytes, offset: 32);
                    if (cmessage_case == 2)
                    {
                        Console.WriteLine("Received a reply with key {0}", reply_key);
                    } else if (cmessage_case == 3)
                    {
                        Console.WriteLine("Received a redirect for key {0}", reply_key);
                    }
                    
                    if (reply_key == request_key && cmessage_case == 2)
                    {
                        received_reply = true;
                    }
                }
            }
        }

        protected override void Experiment(int base_client_port, ulong id, ulong num_keys, ulong size_value, char workload)
        {
            ulong request_key = 150;
            int serverIdx = 0;
            ulong seq_num = 0;
            
            this.udpClient = new System.Net.Sockets.UdpClient(base_client_port + (int)id);
            this.udpClient.Client.ReceiveTimeout = 0;
            uint SIO_UDP_CONNRESET = 0x9800000C; // suppress UDP "connection" closed exceptions, since UDP is connectionless
            this.udpClient.Client.IOControl((System.Net.Sockets.IOControlCode)SIO_UDP_CONNRESET, new byte[] { 0 }, new byte[0]);
            this.udpClient.Client.ReceiveBufferSize = 8192 * 100;

            ulong myaddr = MyAddress64();
            
            
            // Test the functionality of the Sharding
            if (workload == 'f')
            {
                ulong k_lo = 100;
                ulong k_hi = 200;
                var recipient = EncodeIpPort(ClientBase.endpoints[(serverIdx + 1) % ClientBase.endpoints.Count()]);

                seq_num++;

                var msg = new GetRequestMessage(seq_num, myaddr, request_key);
                this.Send(msg, ClientBase.endpoints[serverIdx]);
                ReceiveReply(serverIdx, myaddr, request_key, false);

                seq_num++;
            
                Console.WriteLine("Sending a Shard request with a sequence number {0}", seq_num);
                var shardMessage = new ShardRequestMessage(seq_num, myaddr, k_lo, k_hi, recipient);
                this.Send(shardMessage, ClientBase.endpoints[serverIdx]);
                ReceiveReply(serverIdx, myaddr, request_key, true);

                Thread.Sleep(5000);
                

                Console.WriteLine("Sending a GetRequest after a Shard, expect a redirect");
                seq_num++;
                msg = new GetRequestMessage(seq_num, myaddr, request_key);
                this.Send(msg, ClientBase.endpoints[(serverIdx + 0) % ClientBase.endpoints.Count()]);
                ReceiveReply(serverIdx, myaddr, request_key, false);

                Thread.Sleep(5000);

                Console.WriteLine("Sending a GetRequest after a Shard to the second host, expect a reply");
                seq_num = 1;
                msg = new GetRequestMessage(seq_num, myaddr, request_key);
                this.Send(msg, ClientBase.endpoints[(serverIdx + 1) % ClientBase.endpoints.Count()]);
                ReceiveReply(serverIdx, myaddr, request_key, false);
                
                return;
            }

            // Run an actual workload
            while (true)
            {
                var received_reply = false;
                request_key = seq_num % num_keys;

                seq_num++;
                               
                MessageBase msg;
                if (workload == 'g') 
                {
                    msg = new GetRequestMessage(seq_num, myaddr, request_key);
                }
                else
                {
                    msg = new SetRequestMessage(seq_num, myaddr, request_key, size_value);
                }
                
                var start_time = HiResTimer.Ticks;
                this.Send(msg, ClientBase.endpoints[serverIdx]);
                
                // Wait for the reply
                
                while (!received_reply)
                {
                    byte[] bytes;
                    try
                    {
                        bytes = Receive();
                    }
                    catch (System.Net.Sockets.SocketException)
                    {
                        //serverIdx = (serverIdx + 1) % ClientBase.endpoints.Count();
                        //Console.WriteLine("#timeout; rotating to server {0}", serverIdx);
                        //Console.WriteLine(e.ToString());
                        Console.WriteLine("#timeout; retrying {0}", serverIdx);
                        continue;
                    }
                    var end_time = HiResTimer.Ticks;
                    
                    if (bytes.Length == 16)
                    {
                        //Ignore acks
                    }
                    else if (bytes.Length >= 56) 
                    {
                        var reply_seqno = ExtractBE64(bytes, offset: 8);
                        //Console.Out.WriteLine("Reply sequence number : " + reply_seqno);
                                          

                        //Console.Out.WriteLine("Client " + id.ToString() + ": Sending an ack with a sequence number " + reply_seqno + " to " + ClientBase.endpoints[serverIdx].ToString());
                        if (seq_num % 100 == 0)
                        {
                            var ack_msg = new AckMessage(reply_seqno, myaddr);
                            this.Send(ack_msg, ClientBase.endpoints[serverIdx]);
                        }
                        
                        var reply_key = ExtractBE64(bytes, offset: 32);
                        // Need to send an ack
                        //Console.Out.WriteLine("Request key : " + request_key);
                        //Console.Out.WriteLine("Reply key : " + reply_key);

                        //Console.Out.WriteLine("Got packet length: " + bytes.Length);
                        // key is the same as the sequence number
                        if (reply_key == request_key)
                        {
                            received_reply = true;
                            Console.Out.WriteLine(string.Format("#req{0} {1} {2} {3}", seq_num, (start_time * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3)), (end_time * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3)), id));
                        }
                    }
                    else {
                        Console.Out.WriteLine("Received packet of unexpected length {0}", bytes.Length);
                    }
                }
            }
        }
    }
}
