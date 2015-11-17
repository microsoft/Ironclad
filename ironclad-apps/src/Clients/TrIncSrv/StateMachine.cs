using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Security.Cryptography;
using System.Text;

namespace TrIncSrv
{
    class TrIncCounter
    {
        private RSACryptoServiceProvider public_key;
        private BigInteger counter;

        public RSACryptoServiceProvider PublicKey { get { return public_key; } }
        public BigInteger Value { get { return counter; } set { counter = value; } }

        public TrIncCounter(RSACryptoServiceProvider i_public_key)
        {
            public_key = i_public_key;
            counter = new BigInteger(0);
        }
    }

    class StateMachine
    {
        private RSACryptoServiceProvider key_pair;
        private List<TrIncCounter> counters;
        private SHA256Managed hasher;

        public StateMachine()
        {
            key_pair = new RSACryptoServiceProvider(CommonParams.serverKeyBits);
            counters = new List<TrIncCounter>();
            hasher = new SHA256Managed();
        }

        public byte[] HandleRequest(byte[] requestBytes)
        {
            object request = TrIncRequest.ParseRequest(requestBytes);
            if (request is Common.GetQuoteRequest)
            {
                GetQuoteResponse getQuoteResponse = new GetQuoteResponse(0, key_pair);
                return getQuoteResponse.Encode();
            }
            if (request is CreateCounterRequest)
            {
                CreateCounterRequest r = (CreateCounterRequest)request;
                RSACryptoServiceProvider public_key = CommonRoutines.DecodePublicKey(r.public_key);
                if (public_key == null)
                {
                    return TrIncSrvResponse.EncodeCreateCounterResponse(3, 0);
                }
                TrIncCounter counter = new TrIncCounter(public_key);
                counters.Add(counter);
                UInt32 counter_index = (UInt32)(counters.Count - 1);
                return TrIncSrvResponse.EncodeCreateCounterResponse(0, counter_index);
            }
            if (request is AdvanceCounterRequest)
            {
                AdvanceCounterRequest r = (AdvanceCounterRequest)request;
                if (r.counter_index < 0 || r.counter_index >= counters.Count)
                {
                    Console.Error.WriteLine("Received request for invalid counter index {0}", r.counter_index);
                    return TrIncSrvResponse.EncodeAdvanceCounterResponse(1, new byte[0], new byte[0]);
                }

                TrIncCounter counter = counters[(int)r.counter_index];
                byte[] req = CommonRoutines.CombineByteArrays(r.new_counter_value, r.message);
                if (!counter.PublicKey.VerifyData(req, CryptoConfig.MapNameToOID("SHA256"), r.request_attestation))
                {
                    Console.Error.WriteLine("Received invalid request attestation");
                    return TrIncSrvResponse.EncodeAdvanceCounterResponse(5, new byte[0], new byte[0]);
                }

                int offset = 0;
                BigInteger new_counter_value = CommonRoutines.DecodeMPBigInteger(r.new_counter_value, ref offset);
                if (new_counter_value < 0 || offset != r.new_counter_value.Length)
                {
                    Console.Error.WriteLine("Received invalid new counter value encoding");
                    return TrIncSrvResponse.EncodeAdvanceCounterResponse(6, new byte[0], new byte[0]);
                }

                if (new_counter_value < counter.Value)
                {
                    Console.Error.WriteLine("New counter value requested {0} is smaller than current counter value {1}", new_counter_value, counter.Value);
                    return TrIncSrvResponse.EncodeAdvanceCounterResponse(7, new byte[0], new byte[0]);
                }

                BigInteger old_counter_value = counter.Value;
                counter.Value = new_counter_value;

                byte[] header = new byte[1];
                header[0] = 34;
                byte[] counter_index_encoding = CommonRoutines.EncodeBEWord(r.counter_index);
                byte[] old_counter_value_encoding = CommonRoutines.EncodeMPBigInteger(old_counter_value);
                byte[] new_counter_value_encoding = CommonRoutines.EncodeMPBigInteger(new_counter_value);
                byte[] trinc_statement = CommonRoutines.CombineByteArrays(header, counter_index_encoding, old_counter_value_encoding, new_counter_value_encoding, r.message);
                byte[] trinc_attestation = key_pair.SignData(trinc_statement, CryptoConfig.MapNameToOID("SHA256"));
                return TrIncSrvResponse.EncodeAdvanceCounterResponse(0, trinc_statement, trinc_attestation);
            }
            return InvalidResponse.Encode();
        }
    }
}
