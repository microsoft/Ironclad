using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Numerics;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace Common
{
    public class ErrorCodeException : Exception
    {
        private UInt32 error_code;

        public ErrorCodeException(UInt32 i_error_code)
        {
            error_code = i_error_code;
        }

        public override string ToString()
        {
            return string.Format("Error code {0}", error_code);
        }
    }

    public class InvalidRequest
    {
        public InvalidRequest() { }
    }

    public class InvalidResponse
    {
        public InvalidResponse() { }

        public static byte[] Encode()
        {
            byte[] response = new byte[1];
            response[0] = 0;
            return response;
        }
    }

    public class CommonRoutines
    {
        public static UInt32 ExtractBEWord(byte[] byteArray, int offset)
        {
            byte[] extractedBytes = byteArray.Skip(offset).Take(4).ToArray();
            Array.Reverse(extractedBytes);
            return BitConverter.ToUInt32(extractedBytes, 0);
        }

        public static byte[] EncodeBEWord(UInt32 value)
        {
            byte[] encoding = BitConverter.GetBytes(value);
            Array.Reverse(encoding);
            return encoding;
        }

        public static byte[] EncodeMPInt(UInt32 value)
        {
            Stack<byte> encoding = new Stack<byte>();
            while (value > 0)
            {
                encoding.Push((byte)(value % 256));
                value = value / 256;
            }
            if (encoding.Count != 0 && encoding.Peek() >= 128)
            {
                encoding.Push((byte) 0);
            }
            byte[] length_encoded = EncodeBEWord((uint)encoding.Count);
            byte[] encoding_bytes = encoding.ToArray();
            return CombineByteArrays(length_encoded, encoding_bytes);
        }

        public static byte[] EncodeMPBigInteger(BigInteger value)
        {
            byte[] rawEncoding = value.ToByteArray();
            Array.Reverse(rawEncoding);
            byte[] lengthEncoded = EncodeBEWord((uint)rawEncoding.Length);
            return CombineByteArrays(lengthEncoded, rawEncoding);
        }

        public static UInt32 DecodeShortMPInt(byte[] byteArray, ref int offset)
        {
            if (byteArray.Length < offset + 4)
            {
                throw new Exception("Byte array too short to decode the length of an MPInt from");
            }

            int value_length = (int)ExtractBEWord(byteArray, offset);
            if (byteArray.Length < offset + 4 + value_length)
            {
                throw new Exception("Byte array too short to decode an MPInt from");
            }

            byte[] value_encoded = byteArray.Skip(offset + 4).Take(value_length).ToArray();

            UInt32 value = 0;
            for (int pos = 0; pos < value_encoded.Length; ++pos)
            {
                value = value * 256 + value_encoded[pos];
            }

            offset = offset + 4 + value_length;
            return value;
        }

        public static BigInteger DecodeMPBigInteger(byte[] byteArray, ref int offset)
        {
            if (byteArray.Length < offset + 4)
            {
                return new BigInteger(-1);
            }

            int value_length = (int)ExtractBEWord(byteArray, offset);
            if (byteArray.Length < offset + 4 + value_length)
            {
                return new BigInteger(-1);
            }

            byte[] value_encoded = byteArray.Skip(offset + 4).Take(value_length).ToArray();
            Array.Reverse(value_encoded);
            offset = offset + 4 + value_length;
            return new BigInteger(value_encoded);
        }

        public static byte[] StripProtectiveZero(byte[] mpi)
        {
            if (0 < mpi[0] && mpi[0] < 128)
            {
                return mpi;
            }
            else
            {
                return mpi.Skip(1).ToArray();
            }
        }

        public static RSACryptoServiceProvider DecodePublicKey(byte[] encoded_public_key)
        {
            

            int header_length = (int)ExtractBEWord(encoded_public_key, 0);
            if (header_length != 7)
            {
                Console.WriteLine("Header of encoded public key has invalid length {0} != 7", header_length);
                throw new Exception("Header of encoded public key has invalid length");
            }
            System.Text.UTF8Encoding encoder = new System.Text.UTF8Encoding();
            string header = encoder.GetString(encoded_public_key.Skip(4).Take(header_length).ToArray());
            if (header != "ssh-rsa")
            {
                Console.WriteLine("Header of encoded public key is {0}, not ssh-rsa", header);
                throw new Exception("Header of encoded public key is not ssh-rsa");
            }

            

            int exponent_length = (int)ExtractBEWord(encoded_public_key, 4 + header_length);
            if (encoded_public_key.Length < 4 + header_length + 4 + exponent_length + 4)
            {
                Console.WriteLine("Encoded public key not long enough to hold exponent of length {0}", exponent_length);
                throw new Exception("Encoded public key not long enough to hold exponent");
            }

            

            byte[] exponent = encoded_public_key.Skip(4 + header_length + 4).Take(exponent_length).ToArray();

            

            int modulus_length = (int)ExtractBEWord(encoded_public_key, 4 + header_length + 4 + exponent_length);
            if (encoded_public_key.Length < 4 + header_length + 4 + exponent_length + 4 + modulus_length)
            {
                Console.WriteLine("Encoded public key not long enough to hold modulus of length {0}", modulus_length);
                throw new Exception("Encoded public key not long enough to hold modulus");
            }

            

            byte[] modulus = encoded_public_key.Skip(4 + header_length + 4 + exponent_length + 4).Take(modulus_length).ToArray();

            modulus = StripProtectiveZero(modulus);

            

            RSACryptoServiceProvider provider = new RSACryptoServiceProvider();
            RSAParameters info = new RSAParameters();
            info.Exponent = exponent;
            info.Modulus = modulus;

            try
            {
                provider.ImportParameters(info);
            }
            catch
            {
                if (CommonParams.ignoreKey)
                {
                    return null;
                }
                else
                {
                    throw;
                }
            }

            return provider;
        }

        public static byte[] ParseFakeReply(string pastedhex)
        {
            string[] hexwords = pastedhex.Split(' ');
            int offset = 0x2a;
            byte[] output = new byte[hexwords.Length-offset];
            for (int i = offset; i < hexwords.Length; i++)
            {
                output[i-offset] = Convert.ToByte(hexwords[i], 16);
            }
            return output;
        }

        static public void WriteHexArray(StreamWriter sw, byte[] bytes, string label)
        {
            sw.WriteLine("    var "+label+" = [");
            for (int i=0; i<bytes.Length; i++) {
                sw.Write(String.Format("0x{0:x}", bytes[i]));
                if (i<bytes.Length-1) {
                    sw.Write(",");
                }
            }
            sw.WriteLine("];\n");
        }

        static public void SquirtBakedKey()
        {
            RSACryptoServiceProvider p1 = new RSACryptoServiceProvider(512);
            RSAParameters info1 = p1.ExportParameters(true);
            StreamWriter sw = new StreamWriter("hardcoded-key");
            WriteHexArray(sw, info1.D, "d");
            WriteHexArray(sw, info1.Modulus, "n");
            WriteHexArray(sw, info1.Exponent, "e");
            sw.Close();

            RSACryptoServiceProvider provider = new RSACryptoServiceProvider();
      /*      RSAParameters info = provider.ExportParameters(false);
            //
            
            info.Exponent = exponent;
            
            info.Modulus = modulus;
            provider.ImportParameters(info);*/
            provider.ImportParameters(info1);
        }

        public static byte[] SendRequest(UdpClient client, byte[] request, string profileString = null)
        {
            System.Net.IPEndPoint sender = null;
            Stopwatch stopwatch = null;

            if (profileString != null)
            {
                stopwatch = new Stopwatch();
                stopwatch.Start();
            }

            byte[] response;

            try
            {
                client.Send(request, request.Length);
                response = client.Receive(ref sender);
            }
            catch (SocketException e)
            {
                Console.Error.WriteLine("Caught exception with error code {0}", e.ErrorCode);
                response = new byte[0];
            }

            if (profileString != null)
            {
                stopwatch.Stop();
                Profiler.Record(profileString, stopwatch);
            }

            return response;
        }

        public static RSACryptoServiceProvider GetIroncladPublicKey(UdpClient client)
        {
            GetQuoteRequest getQuoteRequest = new GetQuoteRequest();
            byte[] request = getQuoteRequest.GetPacket();
            byte[] response = CommonRoutines.SendRequest(client, request, "GetIroncladPublicKey");
            GetQuoteResponse getQuoteResponse = new GetQuoteResponse(response);
            return getQuoteResponse.PublicKey;
        }

        public static byte[] CombineByteArrays (params byte[][] arrays)
        {
            byte[] rv = new byte[arrays.Sum(a => a.Length)];
            int offset = 0;
            foreach (byte[] array in arrays) {
                System.Buffer.BlockCopy(array, 0, rv, offset, array.Length);
                offset += array.Length;
            }
            return rv;
        }

        public static byte[] mpint_encode(byte[] raw)
        {
            int i;
            for (i = 0; i < raw.Length-1; i++)
            {
                if (raw[i] != 0)
                {
                    break;
                }
            }
            
            
            raw = raw.Skip(i).ToArray();

            if (raw[0]>=0x80)
            {
                byte[] zero = new byte[1];
                zero[0] = 0;
                raw = CombineByteArrays(zero, raw);
            }
            byte[] length = EncodeBEWord((UInt32)raw.Length);
            return CombineByteArrays(length, raw);
        }

        public static byte[] EncodePublicKey (RSACryptoServiceProvider key_pair)
        {
            RSAParameters rsa_params = key_pair.ExportParameters(false);

            byte[] header = new System.Text.UTF8Encoding().GetBytes("ssh-rsa");
            byte[] header_length = EncodeBEWord((UInt32)header.Length);
            byte[] exponent_encoded = mpint_encode(rsa_params.Exponent);
            byte[] modulus_encoded = mpint_encode(rsa_params.Modulus);

            return CombineByteArrays(header_length, header, exponent_encoded, modulus_encoded);
        }

        public static UInt32[] BEByteSeqToWordSeq(byte[] bytes)
        {
            int num_words = bytes.Length / 4;
            UInt32[] words = new UInt32[num_words];
            for (int i = 0; i < num_words; ++i)
            {
                words[i] = ((UInt32)bytes[i * 4] << 24) + ((UInt32)bytes[i * 4 + 1] << 16) + ((UInt32)bytes[i * 4 + 2] << 8) + (UInt32)bytes[i * 4 + 3];
            }
            return words;
        }

        public static IPEndPoint GetIPEndPoint(string hostname, int port)
        {
            IPHostEntry hostEntry = Dns.GetHostEntry(hostname);
            foreach (IPAddress addr in hostEntry.AddressList)
            {
                if (addr.AddressFamily == AddressFamily.InterNetwork)
                {
                    IPEndPoint ep = new IPEndPoint(addr, port);
                    return ep;
                }
            }
            Console.Error.WriteLine("Could not find address for host name {0}", CommonParams.hostname);
            throw new Exception("Could not find address for host name");
        }

        public static UdpClient StartClient()
        {
            IPEndPoint serverEp = new IPEndPoint(IPAddress.Parse(CommonParams.hostname), CommonParams.port);
            UdpClient client = new UdpClient();
            client.Connect(serverEp);
            return client;
        }

        public static UdpClient StartServer()
        {
            IPEndPoint ep = new IPEndPoint(IPAddress.Parse(CommonParams.hostname), CommonParams.port);
            UdpClient server = new UdpClient(ep);
            return server;
        }
    }
}
