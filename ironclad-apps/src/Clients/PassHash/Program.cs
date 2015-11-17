using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Text;
using System.Threading.Tasks;

namespace PassHash
{
    class Program
    {
        static void PerformHash(UdpClient client, byte[] password, byte[] salt)
        {
            PerformHashRequest performHashRequest = new PerformHashRequest(password, salt);
            byte[] request = performHashRequest.GetPacket();
            byte[] response = CommonRoutines.SendRequest(client, request, "PerformHash");
            PerformHashResponse performHashResponse = new PerformHashResponse(response);
        }

        static void Main(string[] args)
        {
            Parameters.ApplyArguments(args);
            Profiler.Initialize();
            UdpClient client = CommonRoutines.StartClient();

            byte[] password = new byte[Parameters.passwordLength];
            byte[] salt = new byte[Parameters.saltLength];
            Random rng = new Random();
            for (UInt32 run_number = 0; run_number < CommonParams.numberOfRuns; ++run_number)
            {
                Console.Error.WriteLine("Performing run {0}", run_number + 1);
                rng.NextBytes(password);
                rng.NextBytes(salt);
                PerformHash(client, password, salt);
            }

            Profiler.Print();
        }
    }
}
