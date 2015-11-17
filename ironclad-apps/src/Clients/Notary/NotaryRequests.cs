using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace Notary
{
    public class AdvanceCounterRequest
    {
        private byte[] message;

        public AdvanceCounterRequest(byte[] i_message)
        {
            message = i_message;
        }

        public byte[] GetPacket()
        {
            Debug.Assert(message.Length < 256);
            byte[] packet = new byte[2 + message.Length];
            packet[0] = 2;
            packet[1] = (byte)message.Length;
            message.CopyTo(packet, 2);
            return packet;
        }
    }
}
