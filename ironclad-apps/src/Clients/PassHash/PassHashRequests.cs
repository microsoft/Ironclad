using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace PassHash
{
    public class PerformHashRequest
    {
        private byte[] message;
        private byte[] salt;

        public PerformHashRequest(byte[] i_message, byte[] i_salt)
        {
            message = i_message;
            salt = i_salt;
        }

        public byte[] GetPacket()
        {
            byte[] header = new byte[1]; header[0] = 1;
            byte[] message_length_encoded = CommonRoutines.EncodeBEWord((UInt32)message.Length);
            byte[] salt_length_encoded = CommonRoutines.EncodeBEWord((UInt32)salt.Length);
            return CommonRoutines.CombineByteArrays(header, message_length_encoded, salt_length_encoded, message, salt);
        }
    }
}
