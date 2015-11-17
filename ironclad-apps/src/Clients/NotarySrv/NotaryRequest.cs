using Common;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;

namespace NotarySrv
{
    public class NotaryRequest
    {
        public NotaryRequest() { }

        public static object ParseRequest (byte[] request)
        {
            if (request.Length < 1)
            {
                Console.Error.WriteLine("Received request with no bytes");
                return new Common.InvalidRequest();
            }
            if (request[0] == 1)
            {
                return Common.GetQuoteRequest.ParseRequest(request);
            }
            if (request[0] == 2)
            {
                return AdvanceCounterRequest.ParseRequest(request);
            }
            Console.Error.WriteLine("Received request with invalid type");
            return new Common.InvalidRequest();
        }
    }

    public class AdvanceCounterRequest
    {
        public byte[] message;

        public AdvanceCounterRequest(byte[] i_message)
        {
            message = i_message;
        }

        public static object ParseRequest (byte[] request)
        {
            if (request.Length < 2)
            {
                Console.Error.WriteLine("Received advance-counter request with fewer than 2 bytes");
                return new Common.InvalidRequest();
            }
            int messageLength = (int)request[1];
            if (request.Length < 2 + messageLength)
            {
                Console.Error.WriteLine("Received advance-counter request without enough bytes to encode message");
                return new Common.InvalidRequest();
            }
            byte[] message = request.Skip(2).Take(messageLength).ToArray();
            return new AdvanceCounterRequest(message);
        }
    }
}
