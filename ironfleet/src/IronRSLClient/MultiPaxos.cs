namespace IronRSLClient
{
    using System;
    using System.IO;
    using System.Net;
    using System.Threading;
    using System.Diagnostics;
    using System.Linq;

    public class RequestMessage : MessageBase
    {
        public byte[] Value { get; set; }
        public ulong seqNum;
        public ulong myaddr;

        public RequestMessage(ulong seqNum, ulong myaddr)
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

        private byte[] Encode()
        {

            using (var memStream = new MemoryStream())
            {
                this.EncodeHeader(memStream); // case for CMessage_Request
                this.EncodeUlong(memStream, (ulong)seqNum); // field one in CMessage_Request
                this.EncodeUlong(memStream, (ulong)0); // case for CAppMessageIncrement               

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

        protected void ReceiveLoop() {
            byte[] bytes;
            while (true)
            {
                bytes = Receive();
                var end_time = (ulong)HiResTimer.Ticks;
                Trace("Got the following reply:" + ByteArrayToString(bytes));
                if (bytes.Length == 40)
                {
                    var start_time = ExtractBE64(bytes, 32);
                    var request_time = end_time - start_time;

                    Trace("Request took " + request_time + " ticks");
                    Console.WriteLine(request_time);
                }
                else
                {
                    Trace("Got an unexpected packet length: " + bytes.Length);
                }
            }
        }

        protected override void Main(ulong id, int port_num, ulong initial_seq_no)
        {
            this.udpClient = new System.Net.Sockets.UdpClient(port_num+(int)id);
            this.udpClient.Client.ReceiveTimeout = 1000;
            ulong myaddr = MyAddress64();

            int serverIdx = 0;
            
            for (ulong seq_no = initial_seq_no; true; ++seq_no)
            {
                // Make the sequence number a time stamp
                //var newSeqNum = (ulong) HiResTimer.UtcNow.Ticks;
                //if (newSeqNum == seqNum) {
                //    seqNum = newSeqNum + 1;
                //}
                //else
                //{
                //    seqNum = newSeqNum;
                //}

                var msg = new RequestMessage(seq_no, myaddr);

                Trace("Client " + id.ToString() + ": Sending a request with a sequence number " + msg.GetSeqNum() + " to " + ClientBase.endpoints[serverIdx].ToString());

                var start_time = HiResTimer.Ticks;
                this.Send(msg, ClientBase.endpoints[serverIdx]);
                //foreach (var remote in ClientBase.endpoints)
                //{
                //    this.Send(msg, remote);
                //}

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
                        serverIdx = (serverIdx + 1) % ClientBase.endpoints.Count();
                        Console.WriteLine("#timeout; rotating to server {0}", serverIdx);
                        Console.WriteLine(e.ToString());
                        break;
                    }
                    var end_time = HiResTimer.Ticks;
                    Trace("Got the following reply:" + ByteArrayToString(bytes));
                    if (bytes.Length == 32)
                    {
                        var reply_seq_no = ExtractBE64(bytes, offset: 8);
                        if (reply_seq_no == seq_no)
                        {
                            received_reply = true;
                            // Report time in milliseconds, since that's what the Python script appears to expect
                            Console.Out.WriteLine(string.Format("#req{0} {1} {2} {3}", seq_no, (ulong)(start_time * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3)), (ulong)(end_time * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3)), id));
                            //long n = Interlocked.Increment(ref num_reqs);
                            //if (1 == n || n % 1000 == 0)
                            //{
                            //    Console.WriteLine("{0} requests completed.", n);
                            //}
                        }
                    }
                    else
                    {
                        Console.Error.WriteLine("Got an unexpected packet length: " + bytes.Length);
                    }
                }
            }
        }
    }
}
