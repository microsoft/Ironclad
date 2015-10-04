
namespace IronfleetTestDriver
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Runtime.InteropServices;
    using System.Threading;

    public abstract class ClientBase
    {
        private System.Net.Sockets.UdpClient udpClient;

        static public IEnumerable<Thread> StartThreads<T>(int count) where T : ClientBase, new()
        {
            if (count < 0)
            {
                throw new ArgumentException("count is less than 1", "count");
            }

            for (int i = 0; i < count; ++i)
            {
                var t = new Thread(
                    () =>
                        {
                            Thread.Sleep(3000);
                            var c = new T();
                            c.Main();
                        });
                t.Start();
                yield return t;
            }
        }

        public ClientBase()
        {
            this.udpClient = new System.Net.Sockets.UdpClient();
        }

        protected abstract void Main();

        protected void Send(MessageBase msg, System.Net.IPEndPoint remote)
        {
            var a = msg.ToBigEndianByteArray();
            if (this.udpClient.Send(a, a.Length, remote) != a.Length)
            {
                throw new InvalidOperationException("failed to send complete message.");
            }
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
