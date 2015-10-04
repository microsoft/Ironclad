
namespace IronfleetTestDriver
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Net;
    using System.Runtime.InteropServices;
    using System.Threading;
    using System.Linq;
    using System.Threading.Tasks;
    using System.Diagnostics;
    
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
        public ulong num_reqs_at_once;
    }

    public abstract class ClientBase
    {
        protected System.Net.Sockets.UdpClient udpClient;

        public static List<IPEndPoint> endpoints;
        public static IPAddress my_addr;

        public static uint encodedClientAddress()
        {
            //byte[] asbytes = new byte[] { 172, 31, 24, 152 };
            byte[] asbytes = my_addr.GetAddressBytes();
            return ExtractBE32(asbytes, 0);
        }

        public static void StartThread(object p)
        {
            Thread.Sleep(3000);
            var c = new Multipaxos.Client();
            c.Main(((Param)p).id, ((Param)p).num_reqs_at_once);
        }

        static public IEnumerable<Thread> StartThreads<T>(ulong count, bool send_reqs_at_once) where T : ClientBase, new()
        {
            if (count < 0)
            {
                throw new ArgumentException("count is less than 1", "count");
            }

            Param p;
            ulong num_threads;

            if (send_reqs_at_once)
            {
                p.num_reqs_at_once = count;
                num_threads = 1;
            }
            else
            {
                p.num_reqs_at_once = 0;
                num_threads = count;
            }

            for (ulong i = 0; i < num_threads; ++i)
            {
                var t = new Thread(StartThread);

                p.id = i;
                t.Start(p);
                yield return t;
            }
        }

        public ClientBase()
        {
            
        }

        protected abstract void Main(ulong id, ulong num_reqs);

        protected void Send(MessageBase msg, System.Net.IPEndPoint remote)
        {
            var a = msg.ToBigEndianByteArray();
            if (this.udpClient.Send(a, a.Length, remote) != a.Length)
            {
                throw new InvalidOperationException("failed to send complete message.");
            }
        }

        protected byte[] Receive()
        {
            IPEndPoint endpoint = null;
            return this.udpClient.Receive(ref endpoint);          
        }

        // this should really be in the MultiPaxos.cs
        public void UDPListener(ulong num_reqs_at_once)
        {
            bool[] acks = new bool[num_reqs_at_once];

            ulong expected_num_replies = (ulong)(0.9 * num_reqs_at_once);
            
            Task.Run(async () =>
            {
                byte[] bytes;
                var start_time = HiResTimer.Ticks;
                ulong count = expected_num_replies;
                while (true)
                {
                    //IPEndPoint object will allow us to read datagrams sent from any source.
                    var receivedResults = await this.udpClient.ReceiveAsync();
                    bytes = receivedResults.Buffer;
                    
                    if (bytes.Length == 32)
                    {
                        var reply_seq_num = ExtractBE64(bytes, offset: 8);
                        //Console.WriteLine("Got a reply with seq number" + reply_seq_num + " expecting " + expected_num_replies + " replies");
                        if (acks[reply_seq_num] == false)
                        {
                            count--;
                            acks[reply_seq_num] = true;
                            if (count == 0)
                                break;
                        }

                    }
                    else
                    {
                        Console.WriteLine("Got an unexpected reply");
                    }
                }

                var end_time = HiResTimer.Ticks;
                var latency = (ulong)((end_time-start_time) * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3));
                var throughput = (ulong) (expected_num_replies*1000.0/latency);
      
                //Console.Out.WriteLine("num_reqs " + expected_num_replies);
                //Console.Out.WriteLine("latency " + latency + " (ms)");
                //Console.Out.WriteLine("throughput " + throughput + " reqs/s");
                Console.Out.WriteLine(num_reqs_at_once + " " + throughput + " " + latency + " #performance_result");
            });
        }

        public ulong MyAddress64()
        {
            System.Net.IPEndPoint ep = (System.Net.IPEndPoint) udpClient.Client.LocalEndPoint;
            ushort port = (ushort) ep.Port;
            uint addr = encodedClientAddress();
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
}
