using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace PassHash
{
    class PerformHashResponse
    {
        private UInt32 error_code;
        private byte[] hash;

        public UInt32 ErrorCode { get { return error_code; } }

        public PerformHashResponse(byte[] packet)
        {
            if (packet.Length < 37)
            {
                throw new Exception("Invalid PerformHashResponsePacket -- length < 37");
            }
            if (packet[0] != 1)
            {
                throw new Exception("First byte of PerformHashResponse is not 1");
            }
            error_code = CommonRoutines.ExtractBEWord(packet, 1);
            if (error_code != 0)
            {
                throw new ErrorCodeException(error_code);
            }
            hash = packet.Skip(5).Take(32).ToArray();
        }

        public override string ToString()
        {
            return string.Format("PerformHashResponse(error_code={0}", error_code);
        }
    }
}
