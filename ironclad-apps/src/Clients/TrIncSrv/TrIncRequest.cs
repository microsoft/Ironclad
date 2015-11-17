using Common;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;

namespace TrIncSrv
{
    public class TrIncRequest
    {
        public TrIncRequest() { }

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
                return CreateCounterRequest.ParseRequest(request);
            }
            if (request[0] == 3)
            {
                return AdvanceCounterRequest.ParseRequest(request);
            }
            Console.Error.WriteLine("Received request with invalid type");
            return new Common.InvalidRequest();
        }
    }

    public class CreateCounterRequest
    {
        public byte[] public_key;

        public CreateCounterRequest(byte[] i_public_key)
        {
            public_key = i_public_key;
        }

        public static object ParseRequest (byte[] request)
        {
            if (request.Length < 5)
            {
                Console.Error.WriteLine("Received create-counter request with fewer than 5 bytes");
                return new Common.InvalidRequest();
            }
            int public_key_length = (int)CommonRoutines.ExtractBEWord(request, 1);
            if (request.Length < 5 + public_key_length)
            {
                Console.Error.WriteLine("Received create-counter request without enough bytes to encode public key");
                return new Common.InvalidRequest();
            }
            byte[] public_key = request.Skip(5).Take(public_key_length).ToArray();
            return new CreateCounterRequest(public_key);
        }
    }

    public class AdvanceCounterRequest
    {
        public UInt32 counter_index;
        public byte[] new_counter_value;
        public byte[] message;
        public byte[] request_attestation;

        public AdvanceCounterRequest(UInt32 i_counter_index, byte[] i_new_counter_value, byte[] i_message, byte[] i_request_attestation)
        {
            counter_index = i_counter_index;
            new_counter_value = i_new_counter_value;
            message = i_message;
            request_attestation = i_request_attestation;
        }

        public static object ParseRequest (byte[] request)
        {
            if (request.Length < 17)
            {
                Console.Error.WriteLine("Received advance-counter request with fewer than 17 bytes");
                return new Common.InvalidRequest();
            }
            UInt32 counter_index = CommonRoutines.ExtractBEWord(request, 1);
            int new_counter_len = (int)CommonRoutines.ExtractBEWord(request, 5);
            int message_len = (int)CommonRoutines.ExtractBEWord(request, 9);
            int request_attestation_len = (int)CommonRoutines.ExtractBEWord(request, 13);
            if (request.Length < 17 + new_counter_len + message_len + request_attestation_len)
            {
                Console.Error.WriteLine("Received advance-counter request without enough bytes to encode all fields");
                return new Common.InvalidRequest();
            }
            byte[] new_counter_value = request.Skip(17).Take(new_counter_len).ToArray();
            byte[] message = request.Skip(17 + new_counter_len).Take(message_len).ToArray();
            byte[] request_attestation = request.Skip(17 + new_counter_len + message_len).Take(request_attestation_len).ToArray();
            return new AdvanceCounterRequest(counter_index, new_counter_value, message, request_attestation);
        }
    }
}
