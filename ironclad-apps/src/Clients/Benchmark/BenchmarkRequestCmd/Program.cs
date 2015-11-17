//--



//--
namespace Ironclad.Benchmark
{
    using System;
    using Ironclad.Benchmark.Communication;

    /
    /
    /
    public static class Program
    {
        /
        /
        /
        private const ulong CpuSpeed = 2992273000;

        /
        /
        /
        /
        private static void Main(string[] args)
        {
            if (args.Length == 7)
            {
                using (Connection connection = new Connection(args[0]))
                {
                    
                    
                    
                    Request request = new Request();

                    UInt32 useWordsInt, useOriginalInt;
                    if (byte.TryParse(args[1], out request.benchmark) &&
                        UInt32.TryParse(args[2], out request.iterations) &&
                        UInt32.TryParse(args[3], out request.keyLengthInBits) &&
                        UInt32.TryParse(args[4], out request.messageLengthInBits) &&
                        UInt32.TryParse(args[5], out useWordsInt) &&
                        UInt32.TryParse(args[6], out useOriginalInt))
                    {
                       request.useWords = (useWordsInt != 0);
                       request.useOriginal = (useOriginalInt != 0);
                    }
                    else
                    {
                        Usage();
                    }

                    
                    
                    
                    request.SendOnConnection(connection);
                    Console.WriteLine("Request sent.");

                    
                    
                    
                    Response response = new Response(connection);
                    if (response.Error != 0)
                    {
                        Console.WriteLine("Server returned error code 0x{0:x} ({0:d})", response.Error);
                    }
                    else
                    {
                        Console.WriteLine("Response received.");
                        Console.WriteLine();
                        Console.WriteLine("Benchmark: {0:G}", response.Benchmark.ToString());
                        Console.WriteLine("Iterations performed: 0x{0:x}, ({0:d})", response.Iterations);
                        Console.WriteLine("Key bits: 0x{0:x}, ({0:d})", response.keyLengthInBits);
                        Console.WriteLine("Message length in bits: 0x{0:x}, ({0:d})", response.messageLengthInBits);
                        Console.WriteLine("Use words: {0}", response.useWords);
                        Console.WriteLine("Use original: {0}", response.useOriginal);
                        Console.WriteLine("Begin Counter: 0x{0:x16}, ({0:d})", response.BeginCounter);
                        Console.WriteLine("End Counter: 0x{0:x16}, ({0:d})", response.EndCounter);
                        Console.WriteLine("Elapsed Counter: 0x{0:x16}, ({0:d})", response.ElapsedCounter);

                        Console.WriteLine("Elapsed Time (in seconds, assuming a {0} Hertz CPU): {1}", Program.CpuSpeed, response.CalculateElapsedTime(Program.CpuSpeed));
                    }
                }
            }
            else
            {
                Usage();
            }
        }

        /
        /
        /
        private static void Usage()
        {
            Console.WriteLine("Usage: BenchmarkRequestCmd <server> <benchmark> <iterations> <key bits> <message bits> <use words ? 1 : 0> <use original code ? 1 : 0>");
            Environment.Exit(1);
        }
    }
}
