using Common;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Net.Sockets;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace TrInc
{
    class Program
    {
        static RSACryptoServiceProvider CreateNewCounter(UdpClient client, bool counter_index_known, ref UInt32 counter_index)
        {
            CreateCounterRequest createCounterRequest = new CreateCounterRequest(Parameters.publicKeyBits);
            byte[] request = createCounterRequest.GetPacket();
            byte[] response = CommonRoutines.SendRequest(client, request, "CreateNewCounter");
            CreateCounterResponse createCounterResponse = new CreateCounterResponse(response);

            if (counter_index_known && createCounterResponse.CounterIndex != counter_index)
            {
                throw new Exception("New counter index in CreateNewCounterResponse did not match expected counter index");
            }
            counter_index = createCounterResponse.CounterIndex;

            return createCounterRequest.KeyPair;
        }

        static void AdvanceCounter(UdpClient client, RSACryptoServiceProvider ironclad_public_key,
                                   RSACryptoServiceProvider counter_key_pair, SHA256Managed hasher, UInt32 counter_index,
                                   byte[] message, UInt32 old_counter_value, UInt32 new_counter_value)
        {
            AdvanceCounterRequest advanceCounterRequest =
                new AdvanceCounterRequest(counter_index, new_counter_value, message, counter_key_pair);
            byte[] request = advanceCounterRequest.GetPacket(hasher);
            byte[] response = CommonRoutines.SendRequest(client, request, "AdvanceCounter");
            AdvanceCounterResponse advanceCounterResponse = new AdvanceCounterResponse(response, ironclad_public_key);

            if (advanceCounterResponse.OldCounterValue != old_counter_value)
            {
                throw new Exception("AdvanceCounter statement had wrong old counter value");
            }
            if (advanceCounterResponse.NewCounterValue != new_counter_value)
            {
                throw new Exception("AdvanceCounter statement had wrong new counter value");
            }
            if (!advanceCounterResponse.Message.SequenceEqual(message))
            {
                throw new Exception("AdvanceCounter statement had wrong message");
            }
        }

        static void Main(string[] args)
        {
            Parameters.ApplyArguments(args);
            Profiler.Initialize();
            UdpClient client = CommonRoutines.StartClient();

            Console.Error.WriteLine("Getting Ironclad public key");
            RSACryptoServiceProvider ironclad_public_key = CommonRoutines.GetIroncladPublicKey(client);

            Console.Error.WriteLine("Creating TrInc counter for advancing runs");
            UInt32 counter_index = 0;
            RSACryptoServiceProvider counter_key_pair = CreateNewCounter(client, false, ref counter_index);

            Console.Error.WriteLine("Advancing counter {0}", counter_index);

            byte[] message = new byte[Parameters.messageLength];
            Random rng = new Random();
            SHA256Managed hasher = new SHA256Managed();
            for (UInt32 counter_value = 0; counter_value < CommonParams.numberOfRuns; ++counter_value)
            {
                Console.Error.WriteLine("Performing advance-counter run {0}", counter_value + 1);
                rng.NextBytes(message);
                AdvanceCounter(client, ironclad_public_key, counter_key_pair, hasher, counter_index, message, counter_value,
                               counter_value + 1);
            }

            Console.Error.WriteLine("Creating new counters");

            for (UInt32 run_number = 0; run_number < CommonParams.numberOfRuns; ++run_number)
            {
                Console.Error.WriteLine("Performing create-counter run {0}", run_number + 1);
                ++counter_index;
                RSACryptoServiceProvider new_counter_key_pair = CreateNewCounter(client, true, ref counter_index);
            }

            Profiler.Print();
        }
    }
}
