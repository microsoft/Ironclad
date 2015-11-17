using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NotarySrv
{
    class NotarySrvResponse
    {
        public static byte[] EncodeAdvanceCounterResponse (UInt32 error_code, byte[] notary_statement, byte[] notary_attestation)
        {
            byte[] header = new byte[1];
            header[0] = 2;

            byte[] error_code_encoded = CommonRoutines.EncodeBEWord(error_code);
            byte[] notary_statement_length = CommonRoutines.EncodeBEWord((uint)notary_statement.Length);
            byte[] notary_attestation_length = CommonRoutines.EncodeBEWord((uint)notary_attestation.Length);

            return CommonRoutines.CombineByteArrays(header, error_code_encoded, notary_statement_length, notary_attestation_length, notary_statement, notary_attestation);
        }
    }
}
