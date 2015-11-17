using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace PassHashSrv
{
    class PassHashResponse
    {
        public static byte[] EncodePerformHashResponse (UInt32 errorCode, byte[] hash)
        {
            if (hash.Length != 32)
            {
                throw new Exception("Tried to encode hash not of length 32 bytes");
            }

            byte[] response = new byte[37];
            response[0] = 1;
            byte[] encodedErrorCode = CommonRoutines.EncodeBEWord(errorCode);
            Array.Copy(encodedErrorCode, 0, response, 1, 4);
            Array.Copy(hash, 0, response, 5, 32);
            return response;
        }
    }
}
