//--



//--
namespace Ironclad.Benchmark.Communication
{
    using System;
    using System.Net;
    using System.Net.Sockets;

    /
    /
    /
    public class Request
    {
        /
        /
        /
        public byte benchmark;

        /
        /
        /
        public UInt32 iterations;

        /
        /
        /
        public UInt32 keyLengthInBits;

        /
        /
        /
        public bool useWords;

        /
        /
        /
        public bool useOriginal;

        /
        /
        /
        public UInt32 messageLengthInBits;

        /
        /
        /
        public Request()
        {
            this.benchmark = 0;
            this.iterations = 0;
            this.keyLengthInBits = 0;
            this.useWords = false;
	    this.useOriginal = false;
	    this.messageLengthInBits = 0;
        }

        /
        /
        /
        public Benchmark Benchmark
        {
            get { return (Benchmark)this.benchmark; }
            set { this.benchmark = (byte)value; }
        }

        /
        /
        /
        /
        /
        public int SendOnConnection(Connection connection)
        {
            if (connection == null)
            {
                return 0;
            }

            
            
            
            byte[] buffer = new byte[15];
            buffer[0] = this.benchmark;
            byte[] iterationsEncoded = Request.EncodeBEWord(this.iterations);
            iterationsEncoded.CopyTo(buffer, 1);
            byte[] keyLengthEncoded = Request.EncodeBEWord(this.keyLengthInBits);
            keyLengthEncoded.CopyTo(buffer, 5);
            byte[] messageLengthEncoded = Request.EncodeBEWord(this.messageLengthInBits);
            messageLengthEncoded.CopyTo(buffer, 9);
            buffer[13] = (byte)(this.useWords ? 1 : 0);
            buffer[14] = (byte)(this.useOriginal ? 1 : 0);

            return connection.Socket.Send(buffer);
        }

        private static byte[] EncodeBEWord(UInt32 value)
        {
            byte[] encoding = BitConverter.GetBytes(value);
            Array.Reverse(encoding);
            return encoding;
        }
    }
}
