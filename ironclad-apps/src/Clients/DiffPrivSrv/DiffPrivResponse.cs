using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace DiffPrivSrv
{
    class DiffPrivSrvResponse
    {
        public static byte[] EncodeInitializeDBResponse (UInt32 error_code)
        {
            byte[] header = new byte[1];
            header[0] = 2;

            byte[] error_code_encoded = CommonRoutines.EncodeBEWord(error_code);

            return CommonRoutines.CombineByteArrays(header, error_code_encoded);
        }

        public static byte[] EncodeAddRowResponse ()
        {
            byte[] header = new byte[1];
            header[0] = 3;
            return header;
        }

        public static byte[] EncodeQueryResponse (UInt32 error_code, UInt32 response_value)
        {
            byte[] header = new byte[1];
            header[0] = 4;

            byte[] error_code_encoded = CommonRoutines.EncodeBEWord(error_code);
            byte[] response_value_encoded = CommonRoutines.EncodeBEWord((uint)response_value);

            return CommonRoutines.CombineByteArrays(header, error_code_encoded, response_value_encoded);
        }
    }
}
