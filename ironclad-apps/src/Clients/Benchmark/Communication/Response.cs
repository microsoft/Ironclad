using System.Linq;

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
    public class Response
    {
        /
        /
        /
        private byte error;

        /
        /
        /
        private Benchmark benchmark;

        /
        /
        /
        private UInt32 iterations;

        /
        /
        /
        public UInt32 keyLengthInBits;

        /
        /
        /
        public UInt32 messageLengthInBits;

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
        private UInt64 beginCounter;

        /
        /
        /
        private UInt64 endCounter;

        /
        /
        /
        /
        public Response(Connection connection)
        {
            this.benchmark = Benchmark.Nothing;
            this.iterations = 0;
            this.keyLengthInBits = 0;
	    this.messageLengthInBits = 0;
            this.useWords = false;
	    this.useOriginal = false;

            if (connection == null)
            {
                this.error = 1;
                return;
            }

            byte[] buffer = new byte[1500];

            int got = connection.Socket.Receive(buffer);
            if (got < 20)
            {
                this.error = 1;
                return;
            }

#if false
            Console.WriteLine();
            for (int loop = 0; loop < 20; loop++)
            {
                Console.Write("{0:x2} ", buffer[loop]);
            }
            Console.WriteLine();
#endif

            this.error = buffer[0];

            if ((Benchmark)buffer[1] < Benchmark.Max)
            {
                this.benchmark = (Benchmark)buffer[1];
            }
            else
            {
                this.error = 2;
                return;
            }

            this.iterations = Response.ExtractBEWord(buffer, 2);
            this.keyLengthInBits = Response.ExtractBEWord(buffer, 6);
            this.messageLengthInBits = Response.ExtractBEWord(buffer, 10);
            this.useWords = (buffer[14] != 0);
            this.useOriginal = (buffer[15] != 0);

            if (BitConverter.IsLittleEndian)
            {
                byte[] temp = ReverseByteOrder(buffer, 16, 8);
                this.beginCounter = BitConverter.ToUInt64(temp, 0);
                temp = ReverseByteOrder(buffer, 24, 8);
                this.endCounter = BitConverter.ToUInt64(temp, 0);
            }
            else
            {
                this.beginCounter = BitConverter.ToUInt64(buffer, 16);
                this.endCounter = BitConverter.ToUInt64(buffer, 24);
            }
        }

        /
        /
        /
        public byte Error
        {
            get { return this.error; }
        }

        /
        /
        /
        public Benchmark Benchmark
        {
            get { return this.benchmark; }
        }

        /
        /
        /
        public UInt32 Iterations
        {
            get { return this.iterations; }
        }

        /
        /
        /
        public UInt64 BeginCounter
        {
            get { return this.beginCounter; }
        }

        /
        /
        /
        public UInt64 EndCounter
        {
            get { return this.endCounter; }
        }

        /
        /
        /
        public UInt64 ElapsedCounter
        {
            get { return this.endCounter - this.beginCounter; }
        }

        /
        /
        /
        /
        /
        public float CalculateElapsedTime(UInt64 clockSpeedInHertz)
        {
            return (float)this.ElapsedCounter / (float)clockSpeedInHertz;
        }

        /
        /
        /
        /
        /
        /
        /
        private static byte[] ReverseByteOrder(byte[] input, int offset, int length)
        {
            byte[] output = new byte[length];

            for (int index = 0; index < length; index++)
            {
                output[index] = input[offset + length - 1 - index];
            }

            return output;
        }

        private static UInt32 ExtractBEWord(byte[] byteArray, int offset)
        {
            byte[] extractedBytes = byteArray.Skip(offset).Take(4).ToArray();
            Array.Reverse(extractedBytes);
            return BitConverter.ToUInt32(extractedBytes, 0);
        }
    }
}
