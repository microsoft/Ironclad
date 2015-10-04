namespace IronfleetTestDriver.Multipaxos
{
    using System;
    using System.IO;
    using System.Net;
    using System.Threading;

    public class RequestMessage : MessageBase
    {
        public byte[] Value { get; set; }
        public ulong seqNum;

        public RequestMessage(ulong seqNum)
            : base(0)
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
                this.EncodeHeader(memStream); // case for CMessage_Request
                this.EncodeBool(memStream, retrans); // field one in CMessage_Request
                this.EncodeUlong(memStream, (ulong) 0); // case for CValue
                this.EncodeUlong(memStream, (ulong) 0); // case for CAppValue
                this.EncodeUlong(memStream, (ulong) 0); // field one in CAppValue
                this.EncodeUlong(memStream, (ulong) seqNum); // field two in CAppValue

                return memStream.ToArray();
            }
        }
    }

    class Client : ClientBase
    {
        protected override void Main()
        {
            ulong seqNum = 0;
            var remote1 = new System.Net.IPEndPoint(IPAddress.Loopback, 4001);
            var remote2 = new System.Net.IPEndPoint(IPAddress.Loopback, 4002);
            var remote3 = new System.Net.IPEndPoint(IPAddress.Loopback, 4003);
            while (true)
            {
                var msg = new RequestMessage(seqNum);
                seqNum++;
                Console.WriteLine("Client: Sending a request with a sequence number " + msg.GetSeqNum());
                this.Send(msg, remote1);
                this.Send(msg, remote2);
                this.Send(msg, remote3);
                Thread.Sleep(10000);                
            }
        }
    }
}
