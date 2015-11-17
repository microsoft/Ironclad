using Common;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;

namespace PassHashSrv
{
    public class PassHashRequest
    {
        public PassHashRequest() { }

        public static PassHashRequest ParseRequest (byte[] request)
        {
            if (request.Length < 1)
            {
                Console.Error.WriteLine("Received request with no bytes");
                return new InvalidRequest();
            }
            if (request[0] == 1)
            {
                return PerformHashRequest.ParsePassHashRequest(request);
            }
            Console.Error.WriteLine("Received request with invalid type");
            return new InvalidRequest();
        }
    }

    public class InvalidRequest : PassHashRequest
    {
        public InvalidRequest() { }
    }

    public class PerformHashRequest : PassHashRequest
    {
        public byte[] message;
        public byte[] salt;

        public PerformHashRequest(byte[] i_message, byte[] i_salt)
        {
            message = i_message;
            salt = i_salt;
        }

        public static PassHashRequest ParsePassHashRequest (byte[] request)
        {
            if (request.Length < 9)
            {
                Console.Error.WriteLine("Received perform-hash request with fewer than 9 bytes");
                return new InvalidRequest();
            }
            int messageLength = (int)CommonRoutines.ExtractBEWord(request, 1);
            int saltLength = (int)CommonRoutines.ExtractBEWord(request, 5);
            if (request.Length < 9 + messageLength + saltLength)
            {
                Console.Error.WriteLine("Received perform-hash request without enough bytes to encode message and salt");
                return new InvalidRequest();
            }
            byte[] message = request.Skip(9).Take(messageLength).ToArray();
            byte[] salt = request.Skip(9 + messageLength).Take(saltLength).ToArray();
            return new PerformHashRequest(message, salt);
        }
    }
}
