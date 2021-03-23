namespace IronRSLClient
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
        public int port_num;
        public ulong initial_seq_no;
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
            var c = new Client();
            c.Main(((Param)p).id, ((Param)p).port_num, ((Param)p).initial_seq_no);
        }

        static public IEnumerable<Thread> StartThreads<T>(ulong num_threads, int port_num, ulong initial_seq_no) where T : ClientBase, new()
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

        public ClientBase()
        {
            
        }

        protected abstract void Main(ulong id, int port_num, ulong initial_seq_no);

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
