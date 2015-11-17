using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace DiffPriv
{
    class InitializeDBResponse
    {
        private UInt32 error_code;

        public UInt32 ErrorCode { get { return error_code; } }

        public InitializeDBResponse(byte[] packet)
        {
            if (packet.Length < 5)
            {
                throw new Exception("Invalid InitializeDBResponse packet -- length < 5");
            }
            if (packet[0] != 2)
            {
                throw new Exception("First byte of InitializeDBResponse packet is not 2");
            }
            error_code = CommonRoutines.ExtractBEWord(packet, 1);
            if (error_code != 0)
            {
                throw new ErrorCodeException(error_code);
            }
        }

        public override string ToString()
        {
            return string.Format("InitializeDBResponse(error_code={0})", error_code);
        }
    }

    class AddRowResponse
    {
        public AddRowResponse(byte[] packet)
        {
            if (packet.Length < 1)
            {
                throw new Exception("Invalid AddRowResponse packet -- length < 5");
            }
            if (packet[0] != 3)
            {
                throw new Exception("First byte of AddRowResponse packet is not 3");
            }
        }

        public override string ToString()
        {
            return string.Format("AddRowResponse()");
        }
    }

    class QueryResponse
    {
        private UInt32 error_code;
        private UInt32 response_value;

        public UInt32 ErrorCode { get { return error_code; } }
        public UInt32 ResponseValue { get { return response_value; } }

        public QueryResponse(byte[] packet)
        {
            if (packet.Length < 9)
            {
                throw new Exception("Invalid QueryResponse packet -- length < 9");
            }
            if (packet[0] != 4)
            {
                throw new Exception("First byte of QueryResponse packet is not 4");
            }
            error_code = CommonRoutines.ExtractBEWord(packet, 1);
            if (error_code != 0)
            {
                throw new ErrorCodeException(error_code);
            }
            response_value = CommonRoutines.ExtractBEWord(packet, 5);
        }

        public override string ToString()
        {
            return string.Format("QueryResponse(error_code={0})", error_code);
        }
    }
}
