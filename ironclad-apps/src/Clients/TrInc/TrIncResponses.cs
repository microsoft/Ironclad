using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace TrInc
{
    class CreateCounterResponse
    {
        private UInt32 error_code;
        private UInt32 counter_index;

        public UInt32 CounterIndex { get { return counter_index; } }
        public UInt32 ErrorCode { get { return error_code; } }

        public CreateCounterResponse(byte[] packet)
        {
            if (packet.Length < 9)
            {
                throw new Exception("Invalid CreateCounterResponsePacket -- length < 9");
            }
            if (packet[0] != 2)
            {
                throw new Exception("First byte of CreateCounterResponse is not 2");
            }
            error_code = CommonRoutines.ExtractBEWord(packet, 1);
            if (error_code != 0)
            {
                throw new ErrorCodeException(error_code);
            }
            counter_index = CommonRoutines.ExtractBEWord(packet, 5);
        }

        public override string ToString()
        {
            return string.Format("CreateCounterResponse(error_code={0}, counter_index={1})", error_code, counter_index);
        }
    }

    class AdvanceCounterResponse
    {
        private UInt32 error_code;
        private UInt32 counter_index;
        private UInt32 old_counter_value;
        private UInt32 new_counter_value;
        private byte[] message;

        public UInt32 ErrorCode { get { return error_code; } }
        public UInt32 CounterIndex { get { return counter_index; } }
        public UInt32 OldCounterValue { get { return old_counter_value; } }
        public UInt32 NewCounterValue { get { return new_counter_value; } }
        public byte[] Message { get { return message; } }

        public AdvanceCounterResponse(byte[] packet, RSACryptoServiceProvider ironclad_public_key)
        {
            if (packet.Length < 13)
            {
                throw new Exception("Invalid AdvanceCounterResponsePacket -- length < 13");
            }
            if (packet[0] != 3)
            {
                throw new Exception("First byte of AdvanceCounterResponse is not 3");
            }
            error_code = CommonRoutines.ExtractBEWord(packet, 1);
            if (error_code != 0)
            {
                throw new ErrorCodeException(error_code);
            }
            int trinc_statement_length = (int)CommonRoutines.ExtractBEWord(packet, 5);
            int trinc_attestation_length = (int)CommonRoutines.ExtractBEWord(packet, 9);
            byte[] trinc_statement = packet.Skip(13).Take(trinc_statement_length).ToArray();
            byte[] trinc_attestation = packet.Skip(13 + trinc_statement_length).Take(trinc_attestation_length).ToArray();

            if (trinc_statement.Length < 1)
            {
                throw new Exception("TrInc statement too short");
            }
            if (trinc_statement[0] != 34)
            {
                throw new Exception("TrInc statement does not start with magic byte 34");
            }

            counter_index = CommonRoutines.ExtractBEWord(trinc_statement, 1);
            int offset = 5;
            old_counter_value = CommonRoutines.DecodeShortMPInt(trinc_statement, ref offset);
            new_counter_value = CommonRoutines.DecodeShortMPInt(trinc_statement, ref offset);
            message = trinc_statement.Skip(offset).ToArray();

            if (!CommonParams.ignoreKey &&
                !ironclad_public_key.VerifyData(trinc_statement, CryptoConfig.MapNameToOID("SHA256"), trinc_attestation))
            {
                throw new Exception("Could not verify signature of TrInc statement");
            }
        }

        public override string ToString()
        {
            return string.Format("AdvanceCounterResponse(error_code={0}", error_code);
        }
    }
}
