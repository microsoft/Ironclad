using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace TrIncSrv
{
    class TrIncSrvResponse
    {
        public static byte[] EncodeCreateCounterResponse (UInt32 error_code, UInt32 counter_index)
        {
            byte[] header = new byte[1];
            header[0] = 2;

            byte[] error_code_encoded = CommonRoutines.EncodeBEWord(error_code);
            byte[] counter_index_encoded = CommonRoutines.EncodeBEWord((uint)counter_index);

            return CommonRoutines.CombineByteArrays(header, error_code_encoded, counter_index_encoded);
        }

        public static byte[] EncodeAdvanceCounterResponse (UInt32 error_code, byte[] trinc_statement, byte[] trinc_attestation)
        {
            byte[] header = new byte[1];
            header[0] = 3;

            byte[] error_code_encoded = CommonRoutines.EncodeBEWord(error_code);
            byte[] trinc_statement_length = CommonRoutines.EncodeBEWord((uint)trinc_statement.Length);
            byte[] trinc_attestation_length = CommonRoutines.EncodeBEWord((uint)trinc_attestation.Length);

            return CommonRoutines.CombineByteArrays(header, error_code_encoded, trinc_statement_length, trinc_attestation_length, trinc_statement, trinc_attestation);
        }
    }
}
