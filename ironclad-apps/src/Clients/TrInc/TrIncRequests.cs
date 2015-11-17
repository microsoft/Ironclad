using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace TrInc
{
    public class CreateCounterRequest
    {
        private int key_size;
        private RSACryptoServiceProvider key_pair;

        public RSACryptoServiceProvider KeyPair { get { return key_pair; } }

        public CreateCounterRequest(int i_key_size)
        {
            key_size = i_key_size;
            key_pair = new RSACryptoServiceProvider(key_size);
        }

        public byte[] GetPacket()
        {
            byte[] header = new byte[1]; header[0] = 2;
            byte[] encoded_public_key = CommonRoutines.EncodePublicKey(key_pair);
            byte[] encoded_public_key_length = CommonRoutines.EncodeBEWord((UInt32)encoded_public_key.Length);
            return CommonRoutines.CombineByteArrays(header, encoded_public_key_length, encoded_public_key);
        }
    }

    public class AdvanceCounterRequest
    {
        private UInt32 counter_index;
        private UInt32 new_counter_value;
        private byte[] message;
        private RSACryptoServiceProvider key_pair;

        public AdvanceCounterRequest(UInt32 i_counter_index, UInt32 i_new_counter_value, byte[] i_message, RSACryptoServiceProvider i_key_pair)
        {
            counter_index = i_counter_index;
            new_counter_value = i_new_counter_value;
            message = i_message;
            key_pair = i_key_pair;
        }

        public byte[] GetPacket(SHA256Managed hasher)
        {
            byte[] header = new byte[1]; header[0] = 3;
            byte[] counter_index_encoded = CommonRoutines.EncodeBEWord(counter_index);

            byte[] new_counter_value_encoded = CommonRoutines.EncodeMPInt(new_counter_value);
            byte[] new_counter_value_length_encoded = CommonRoutines.EncodeBEWord((UInt32)new_counter_value_encoded.Length);

            byte[] message_length_encoded = CommonRoutines.EncodeBEWord((UInt32) message.Length);

            byte[] request = CommonRoutines.CombineByteArrays(new_counter_value_encoded, message);
            byte[] request_attestation = key_pair.SignData(request, CryptoConfig.MapNameToOID("SHA256"));
            byte[] request_attestation_length_encoded = CommonRoutines.EncodeBEWord((UInt32)request_attestation.Length);

            return CommonRoutines.CombineByteArrays(header, counter_index_encoded, new_counter_value_length_encoded, message_length_encoded,
                                                    request_attestation_length_encoded, new_counter_value_encoded, message,
                                                    request_attestation);
        }
    }
}
