using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;

namespace PassHashSrv
{
    class StateMachine
    {
        private byte[] secret;
        private SHA256 hasher;

        public StateMachine()
        {
            secret = new byte[Parameters.secretLength];
            Random rng = new Random();
            rng.NextBytes(secret);
            hasher = new SHA256Managed();
        }

        public byte[] HandleRequest(byte[] requestBytes)
        {
            PassHashRequest request = PassHashRequest.ParseRequest(requestBytes);
            if (request is PerformHashRequest)
            {
                PerformHashRequest performHashRequest = (PerformHashRequest)request;
                byte[] message = performHashRequest.message;
                byte[] salt = performHashRequest.salt;

                byte[] mashup = CommonRoutines.CombineByteArrays(secret, salt, message);
                byte[] hash = hasher.ComputeHash(mashup);
                return PassHashResponse.EncodePerformHashResponse(0, hash);
            }
            else
            {
                return Common.InvalidResponse.Encode();
            }
        }
    }
}
