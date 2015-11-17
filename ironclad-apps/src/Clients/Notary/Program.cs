using Common;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace Notary
{
    class Program
    {
        static void AdvanceCounter(UdpClient client, RSACryptoServiceProvider ironclad_public_key, byte[] message,
                                   bool new_counter_value_known, ref UInt32 new_counter_value)
        {
            AdvanceCounterRequest advanceCounterRequest = new AdvanceCounterRequest(message);
            byte[] request = advanceCounterRequest.GetPacket();
            byte[] response = CommonRoutines.SendRequest(client, request, "AdvanceCounter");
            AdvanceCounterResponse advanceCounterResponse = new AdvanceCounterResponse(response, ironclad_public_key);

            if (new_counter_value_known && advanceCounterResponse.NewCounterValue != new_counter_value)
            {
                throw new Exception("New counter value in AdvanceCounterResponse did not match expected counter value");
            }
            new_counter_value = advanceCounterResponse.NewCounterValue;

            if (!advanceCounterResponse.Message.SequenceEqual(message))
            {
                throw new Exception("Message in AdvanceCounterResponse did not match expected message");
            }
        }

        static void TestStuff()
        {
            CommonRoutines.SquirtBakedKey();
            byte[] getQuoteResponseBytes = CommonRoutines.ParseFakeReply("68 05 CA 1A 1D 69 00 1B 21 31 8E D9 08 00 45 00 01 80 00 00 00 00 80 11 11 3C 0A 0A 0A 14 0A 0A 0A 0A 07 BF F4 96 01 6C 3F C7 01 00 00 00 00 00 00 00 57 00 00 01 00 00 00 00 07 73 73 68 2D 72 73 61 00 00 00 03 01 00 01 00 00 00 41 00 A9 52 43 21 04 37 54 10 11 92 9F 70 A8 D3 3B 4A 44 F3 62 C3 47 89 78 93 3E 38 D8 B8 FF 33 32 3F F8 8D 03 3B B0 D7 81 47 1A 79 75 A6 6F 38 57 D9 E7 82 9D 8D 51 7F 40 BA 50 4E 22 B5 95 95 13 B5 2A 5F C5 F6 6C F3 73 85 94 D2 72 4F A3 D9 C1 8E A9 09 7B 32 2F 38 14 FD 50 22 D1 FE B1 0B 16 CD 0B 5E D7 1B 5A CF 34 14 04 4D 49 91 25 44 A3 4C 4B 3E 01 B4 14 4F 33 FA D3 9B 84 A4 4A 23 7F 13 10 0E D4 FB EC 74 53 FD 52 62 95 8A AF D6 FC B6 DB 5B 07 43 3E 70 12 5E 71 9B 15 EB 82 81 60 01 0E A2 87 A0 86 12 E0 71 17 4E 2C 4F 4C 0E 29 57 D5 F2 73 8E 52 72 14 96 CD 19 17 60 AC D2 4C 02 5D EE D5 A7 D0 D4 14 F4 FE B0 71 8A 08 C7 86 94 0E B9 7F E9 ED E2 5C 97 30 C2 6C E0 72 2A CF EE BE 52 D1 32 48 75 00 0D 3C DA ED AA 5D 35 DC 0B B4 40 8D DB 65 F7 C1 56 54 D9 44 85 D1 1E 34 D1 17 A5 A9 41 9E 68 CD 0E 4C E1 BF 30 65 E3 0E 95 A2 46 EF A5 23 B5 5E 68 EA 1D 08 8A 12 19 57 05 34 B8 2E 71 DA 67 84 55 BB 74 92 D4 F3 B9 61 BE 56 8E D8 65 33 82 3E 7E 69 AF F1 92 59 CD 47 3F");
            GetQuoteResponse gr = new GetQuoteResponse(getQuoteResponseBytes);
            byte[] advanceCounterResponseBytes = CommonRoutines.ParseFakeReply("68 05 CA 1A 1D 69 00 1B 21 31 8E D9 08 00 45 00 00 70 00 00 00 00 80 11 12 4C 0A 0A 0A 14 0A 0A 0A 0A 07 BF F4 96 00 5C B6 A7 02 00 00 00 00 00 00 00 07 00 00 00 40 22 00 00 00 01 01 64 03 FC D3 33 B6 D2 25 38 08 7E FD 31 E6 64 D5 A9 C0 5D 26 E1 2E 4C 97 8D AC D5 EA 6D 50 5A C6 EF 98 62 DC 4B 54 AF 32 96 E3 5D EF 96 D3 B6 83 D3 80 8F 68 EE 8F 3E 9F 7C 9C B2 EB 50 EF F4 52 3B");
            AdvanceCounterResponse a = new AdvanceCounterResponse(advanceCounterResponseBytes, gr.PublicKey);
            while (true) { }
        }

        static void Main(string[] args)
        {
            Parameters.ApplyArguments(args);
            Profiler.Initialize();
            UdpClient client = CommonRoutines.StartClient();

            Console.Error.WriteLine("Getting Ironclad public key");
            RSACryptoServiceProvider ironclad_public_key = CommonRoutines.GetIroncladPublicKey(client);

/*
            for (UInt32 run_number = 1; run_number < CommonParams.numberOfRuns; ++run_number)
            {
                GetQuoteRequest getQuoteRequest = new GetQuoteRequest();
                byte[] request = getQuoteRequest.GetPacket();
                byte[] response = CommonRoutines.SendRequest(client, request, "GetIroncladPublicKey");
            }
*/ 

            byte[] message = new byte[Parameters.messageLength];
            Random rng = new Random();
            UInt32 last_counter_value = 0;

            for (UInt32 run_number = 0; run_number < CommonParams.numberOfRuns; ++run_number)
            {
                Console.Error.WriteLine("Performing run {0}", run_number + 1);
                rng.NextBytes(message);
                if (run_number == 0)
                {
                    AdvanceCounter(client, ironclad_public_key, message, false, ref last_counter_value);
                }
                else
                {
                    last_counter_value++;
                    AdvanceCounter(client, ironclad_public_key, message, true, ref last_counter_value);
                }
            }

            Profiler.Print();
        }
    }
}
