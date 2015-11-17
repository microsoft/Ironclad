using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace Common
{
    public class GetQuoteRequest
    {
        private byte[] nonce;

        public GetQuoteRequest()
        {
            Random rng = new Random();
            nonce = new byte[20];
            rng.NextBytes(nonce);
        }

        public GetQuoteRequest(byte[] i_nonce)
        {
            nonce = i_nonce;
        }

        public byte[] GetPacket()
        {
            Random rng = new Random();
            byte[] packet = new byte[21];
            packet[0] = 1;
            nonce.CopyTo(packet, 1);
            return packet;
        }

        public static object ParseRequest (byte[] packet)
        {
            if (packet.Length < 21)
            {
                Console.Error.WriteLine("Received get-quote request with fewer than 21 bytes");
                return new InvalidRequest();
            }
            byte[] nonce = packet.Skip(1).Take(20).ToArray();
            return new GetQuoteRequest(nonce);
        }
    }

    public class GetQuoteResponse
    {
        private UInt32 error_code;
        private RSACryptoServiceProvider public_key;
        private byte[] pcr_info;
        private byte[] sig;

        public RSACryptoServiceProvider PublicKey { get { return public_key; } }

        public GetQuoteResponse(byte[] packet)
        {
            if (packet.Length < 17)
            {
                throw new Exception("Invalid GetQuoteResponse packet -- length < 17");
            }
            if (packet[0] != 1)
            {
                throw new Exception("First byte of GetQuoteResponse is not 1");
            }
            error_code = CommonRoutines.ExtractBEWord(packet, 1);
            if (error_code != 0)
            {
                throw new ErrorCodeException(error_code);
            }
            int encoded_public_key_length = (int)CommonRoutines.ExtractBEWord(packet, 5);
            int pcr_info_bytes_length = (int)CommonRoutines.ExtractBEWord(packet, 9);
            int sig_bytes_length = (int)CommonRoutines.ExtractBEWord(packet, 13);
            if (packet.Length < 17 + encoded_public_key_length + pcr_info_bytes_length + sig_bytes_length)
            {
                throw new Exception("Invalid GetQuoteResponse packet -- length not big enough");
            }
            byte[] encoded_public_key = packet.Skip(17).Take(encoded_public_key_length).ToArray();
            pcr_info = packet.Skip(17 + encoded_public_key_length).Take(pcr_info_bytes_length).ToArray();
            sig = packet.Skip(17 + encoded_public_key_length + pcr_info_bytes_length).Take(sig_bytes_length).ToArray();

            CheckPCRInfo(pcr_info, encoded_public_key);

            public_key = CommonRoutines.DecodePublicKey(encoded_public_key);
        }

        public GetQuoteResponse (UInt32 i_error_code, RSACryptoServiceProvider i_public_key)
        {
            error_code = i_error_code;
            public_key = i_public_key;

            pcr_info = new byte[25];
            pcr_info[0] = 0;
            pcr_info[1] = 3;
            pcr_info[2] = 0;
            pcr_info[3] = 0;
            pcr_info[4] = 14;
            if (CommonParams.loaderHash.Length == 40 && CommonParams.appHash.Length == 40) {
                SHA1Managed hasher = new SHA1Managed();
                byte[] encoded_public_key = CommonRoutines.EncodePublicKey(public_key);
                byte[] pcr17 = GetExpectedPCR17();
                byte[] pcr18 = GetZeroPCR();
                byte[] pcr19 = GetExpectedPCR19(hasher, encoded_public_key);
                byte[] tpm_pcr_composite = CommonRoutines.CombineByteArrays(pcr_info.Take(5).ToArray(), BitConverter.GetBytes((UInt32)60), pcr17, pcr18, pcr19);
                byte[] h1 = hasher.ComputeHash(tpm_pcr_composite);
                Array.Copy(h1, 0, pcr_info, 5, 20);
            }

            sig = new byte[1];
            sig[0] = 0;
        }

        public override string ToString()
        {
            return string.Format("GetQuoteResponse(error_code={0}, public_key={1}, pcr_info={2}, sig={3})", error_code, public_key, pcr_info, sig);
        }

        private byte[] GetZeroPCR()
        {
            byte[] values = new byte[20];
            for (int i = 0; i < 20; ++i)
            {
                values[i] = 0;
            }
            return values;
        }

        private byte[] ExtendPCR(SHA1Managed hasher, byte[] currentValue, byte[] valueToExtendBy)
        {
            return hasher.ComputeHash(CommonRoutines.CombineByteArrays(currentValue, valueToExtendBy));
        }

        private byte[] ConvertHexStringToByteArray(string hex)
        {
            int num_bytes = hex.Length / 2;
            byte[] arr = new byte[num_bytes];
            for (int i = 0; i < num_bytes; ++i)
            {
                arr[i] = Convert.ToByte(hex.Substring(i * 2, 2), 16);
            }
            return arr;
        }

        private byte[] GetExpectedPCR17()
        {
            return ConvertHexStringToByteArray(CommonParams.loaderHash);
        }

        private byte[] GetExpectedPCR19(SHA1Managed hasher, byte[] encoded_public_key)
        {
            byte[] pcr = GetZeroPCR();
            pcr = ExtendPCR(hasher, pcr, ConvertHexStringToByteArray(CommonParams.appHash));
            pcr = ExtendPCR(hasher, pcr, hasher.ComputeHash(encoded_public_key));
            return pcr;
        }

        private void CheckPCRInfo(byte[] pcr_info, byte[] encoded_public_key)
        {
            if (pcr_info[0] != 0 || pcr_info[1] != 3 || pcr_info[2] != 0 || pcr_info[3] != 0 || pcr_info[4] != 14)
            {
                throw new Exception("Invalid PCR selection in PCR info");
            }

            if (CommonParams.loaderHash.Length != 40 || CommonParams.appHash.Length != 40)
            {
                Console.Error.WriteLine("Skipping TPM composite hash check because loader hash and app hash weren't supplied");
                return;
            }

            SHA1Managed hasher = new SHA1Managed();
            byte[] pcr17 = GetExpectedPCR17();
            byte[] pcr18 = GetZeroPCR();
            byte[] pcr19 = GetExpectedPCR19(hasher, encoded_public_key);
            byte[] tpm_pcr_composite = CommonRoutines.CombineByteArrays(pcr_info.Take(5).ToArray(), BitConverter.GetBytes((UInt32)60), pcr17, pcr18, pcr19);
            byte[] h1 = hasher.ComputeHash(tpm_pcr_composite);

            byte[] received_h1 = pcr_info.Skip(5).Take(20).ToArray();

            if (!h1.SequenceEqual(received_h1))
            {
                throw new Exception("Composite hash in received PCR info not what was expected");
            }
        }

        public byte[] Encode ()
        {
            byte[] header = new byte[1];
            header[0] = 1;

            byte[] error_code = CommonRoutines.EncodeBEWord(0);

            byte[] encoded_public_key = CommonRoutines.EncodePublicKey(public_key);
            byte[] encoded_public_key_length = CommonRoutines.EncodeBEWord((uint)encoded_public_key.Length);

            byte[] pcr_info_length = CommonRoutines.EncodeBEWord((uint)pcr_info.Length);
            byte[] sig_length = CommonRoutines.EncodeBEWord((uint)sig.Length);

            return CommonRoutines.CombineByteArrays(header, error_code, encoded_public_key_length, pcr_info_length, sig_length, encoded_public_key, pcr_info, sig);
        }
    }
}
