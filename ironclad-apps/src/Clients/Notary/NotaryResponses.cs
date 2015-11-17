using Common;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Net.Sockets;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace Notary
{
    class AdvanceCounterResponse
    {
        private UInt32 error_code;
        private UInt32 new_counter_value;
        private byte[] message;

        public UInt32 ErrorCode { get { return error_code; } }
        public UInt32 NewCounterValue { get { return new_counter_value; } }
        public byte[] Message { get { return message; } }

        public AdvanceCounterResponse(byte[] packet, RSACryptoServiceProvider ironclad_public_key)
        {
            if (packet.Length < 13)
            {
                throw new Exception("Invalid AdvanceCounterResponsePacket -- length < 13");
            }
            if (packet[0] != 2)
            {
                throw new Exception("First byte of AdvanceCounterResponse is not 2");
            }
            error_code = CommonRoutines.ExtractBEWord(packet, 1);
            if (error_code != 0)
            {
                throw new ErrorCodeException(error_code);
            }
            int notary_statement_length = (int)CommonRoutines.ExtractBEWord(packet, 5);
            int notary_attestation_length = (int)CommonRoutines.ExtractBEWord(packet, 9);
            byte[] notary_statement = packet.Skip(13).Take(notary_statement_length).ToArray();
            byte[] notary_attestation = packet.Skip(13 + notary_statement_length).Take(notary_attestation_length).ToArray();

            if (notary_statement.Length < 1)
            {
                throw new Exception("Notary statement too short");
            }
            if (notary_statement[0] != 34)
            {
                throw new Exception("Notary statement does not start with magic byte 34");
            }

            int offset = 1;
            new_counter_value = CommonRoutines.DecodeShortMPInt(notary_statement, ref offset);
            message = notary_statement.Skip(offset).ToArray();

            if (!CommonParams.ignoreKey &&
                !ironclad_public_key.VerifyData(notary_statement, CryptoConfig.MapNameToOID("SHA256"), notary_attestation))
            {
                throw new Exception("Could not verify signature of notary statement");
            }
        }

        public override string ToString()
        {
            return string.Format("AdvanceCounterResponse(error_code={0}", error_code);
        }
    }
}
