using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Security.Cryptography;
using System.Text;

namespace NotarySrv
{
    class StateMachine
    {
        private RSACryptoServiceProvider key_pair;
        private BigInteger counter;

        public StateMachine()
        {
            key_pair = new RSACryptoServiceProvider(CommonParams.serverKeyBits);
            counter = new BigInteger(0);
        }

        public byte[] HandleRequest(byte[] requestBytes)
        {
            object request = NotaryRequest.ParseRequest(requestBytes);
            if (request is Common.GetQuoteRequest)
            {
                GetQuoteResponse getQuoteResponse = new GetQuoteResponse(0, key_pair);
                return getQuoteResponse.Encode();
            }
            if (request is AdvanceCounterRequest)
            {
                AdvanceCounterRequest r = (AdvanceCounterRequest)request;
                counter = counter + 1;
                byte[] header = new byte[1];
                header[0] = 34;
                byte[] new_counter_value_encoding = CommonRoutines.EncodeMPBigInteger(counter);
                byte[] notary_statement = CommonRoutines.CombineByteArrays(header, new_counter_value_encoding, r.message);
                byte[] notary_attestation = key_pair.SignData(notary_statement, CryptoConfig.MapNameToOID("SHA256"));
                return NotarySrvResponse.EncodeAdvanceCounterResponse(0, notary_statement, notary_attestation);
            }
            return InvalidResponse.Encode();
        }
    }
}
