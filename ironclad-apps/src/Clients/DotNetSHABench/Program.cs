using Common;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace DotNetSHABench
{
    class Program
    {
        static void TestSHA (int message_size, int num_runs)
        {
            string profileID = string.Format("SHA256-{0}Bytes", message_size);
            SHA256Managed hasher = new SHA256Managed();
            byte[] message = new byte[message_size];
            Random rng = new Random();
            Stopwatch stopwatch = new Stopwatch();
            for (int run_number = 0; run_number < Parameters.numberOfRuns; ++run_number)
            {
                rng.NextBytes(message);
                stopwatch.Restart();
                byte[] hash = hasher.ComputeHash(message);
                stopwatch.Stop();
                Profiler.Record(profileID, stopwatch);
            }
        }

        static void DoAllTests()
        {
            Stopwatch stopwatch = new Stopwatch();
            int run_number = 0;
            SHA1Managed sha1_hasher = new SHA1Managed();
            SHA256Managed sha256_hasher = new SHA256Managed();
            byte[] msg32 = new byte[32];
            byte[] msg256 = new byte[256];
            byte[] msg8192 = new byte[8192];
            Random rng = new Random();
            rng.NextBytes(msg32);
            rng.NextBytes(msg256);
            rng.NextBytes(msg8192);
            double usec_per_op;
            double msec_per_op;
            double nsec_per_byte;
            byte[] hash;
            byte[] encrypted = null;
            byte[] decrypted;
            RSACryptoServiceProvider key_pair = null;
            RSAParameters p;

            stopwatch.Restart();
            for (run_number = 0; run_number < Parameters.numberOfRuns; ++run_number)
            {
                key_pair = new RSACryptoServiceProvider(1024);
                p = key_pair.ExportParameters(true);
            }
            stopwatch.Stop();
            msec_per_op = stopwatch.ElapsedTicks * 1000.0 / Stopwatch.Frequency / Parameters.numberOfRuns;
            Console.WriteLine("RSA KeyGen\t1024b\t{0} ms/op", msec_per_op);

            stopwatch.Restart();
            for (run_number = 0; run_number < Parameters.numberOfRuns; ++run_number)
            {
                encrypted = key_pair.Encrypt(msg32, false);
            }
            stopwatch.Stop();
            usec_per_op = stopwatch.ElapsedTicks * 1000000.0 / Stopwatch.Frequency / Parameters.numberOfRuns;
            Console.WriteLine("RSA Public\t1024b\t{0} us/op", usec_per_op);

            stopwatch.Restart();
            for (run_number = 0; run_number < Parameters.numberOfRuns; ++run_number)
            {
                decrypted = key_pair.Decrypt(encrypted, false);
            }
            stopwatch.Stop();
            usec_per_op = stopwatch.ElapsedTicks * 1000000.0 / Stopwatch.Frequency / Parameters.numberOfRuns;
            Console.WriteLine("RSA Private\t1024b\t{0} us/op", usec_per_op);

/*
            stopwatch.Restart();
            for (run_number = 0; run_number < Parameters.numberOfRuns; ++run_number)
            {
                hash = sha1_hasher.ComputeHash(msg256);
            }
            stopwatch.Stop();
            usec_per_op = stopwatch.ElapsedTicks * 1000000.0 / Stopwatch.Frequency / Parameters.numberOfRuns;
            nsec_per_byte = usec_per_op * 1000.0 / 256;
            Console.WriteLine("SHA-1\t256B\t{0} us/op\t{1} ns/B", usec_per_op, nsec_per_byte);

            stopwatch.Restart();
            for (run_number = 0; run_number < Parameters.numberOfRuns; ++run_number)
            {
                hash = sha1_hasher.ComputeHash(msg8192);
            }
            stopwatch.Stop();
            usec_per_op = stopwatch.ElapsedTicks * 1000000.0 / Stopwatch.Frequency / Parameters.numberOfRuns;
            nsec_per_byte = usec_per_op * 1000.0 / 8192;
            Console.WriteLine("SHA-1\t8192B\t{0} us/op\t{1} ns/B", usec_per_op, nsec_per_byte);
*/

            stopwatch.Restart();
            for (run_number = 0; run_number < Parameters.numberOfRuns; ++run_number)
            {
                hash = sha256_hasher.ComputeHash(msg256);
            }
            stopwatch.Stop();
            usec_per_op = stopwatch.ElapsedTicks * 1000000.0 / Stopwatch.Frequency / Parameters.numberOfRuns;
            nsec_per_byte = usec_per_op * 1000.0 / 256;
            Console.WriteLine("SHA-256\t256B\t{0} us/op\t{1} ns/B", usec_per_op, nsec_per_byte);

            stopwatch.Restart();
            for (run_number = 0; run_number < Parameters.numberOfRuns; ++run_number)
            {
                hash = sha1_hasher.ComputeHash(msg8192);
            }
            stopwatch.Stop();
            usec_per_op = stopwatch.ElapsedTicks * 1000000.0 / Stopwatch.Frequency / Parameters.numberOfRuns;
            nsec_per_byte = usec_per_op * 1000.0 / 8192;
            Console.WriteLine("SHA-256\t8192B\t{0} us/op\t{1} ns/B", usec_per_op, nsec_per_byte);
        }

        static void Main(string[] args)
        {
            Parameters.ApplyArguments(args);
            DoAllTests();
/*
            Profiler.Initialize();
            TestSHA(Parameters.messageSize, Parameters.numberOfRuns);
            Profiler.Print();
*/ 
        }
    }
}
