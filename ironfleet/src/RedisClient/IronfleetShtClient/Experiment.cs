using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace IronfleetShtClient
{
    using System.Diagnostics;
    using System.IO;
    using System.Security.Cryptography;
    using System.Threading;

    public abstract class Experiment
    {
        private readonly long durationMs;

        private readonly long durationTicks;

        private TextWriter textWriter;

        private readonly Thread[] threads;

        private KeyValueStoreClient[] clients;

        private readonly Barrier startBarrier;

        private Func<KeyValueStoreClient> connect; 


        protected Experiment(Func<KeyValueStoreClient> connect, int clientCount, long durationMs, TextWriter textWriter)
        {
            if (null == connect)
            {
                throw new ArgumentNullException("connect");
            }

            if (clientCount < 1)
            {
                throw new ArgumentOutOfRangeException("clientCount is less than 1.");
            }

            if (durationMs < 1)
            {
                throw new ArgumentOutOfRangeException("duration is less than 1 millisecond.");
            }

            this.connect = connect;
            this.durationMs = durationMs;
            this.durationTicks = TimeSpan.FromMilliseconds(durationMs).Ticks;
            this.textWriter = textWriter ?? Console.Out;
            this.startBarrier = new Barrier(clientCount + 1);
            this.threads = new Thread[clientCount];
            this.clients = new KeyValueStoreClient[clientCount];
        }

        public void Perform(Random rng)
        {
            Debug.Assert(this.textWriter != null, "the text writer reference cannot be null.");
            Console.Out.WriteLine("Starting {0} threads...", this.threads.Length);

            for (var i = 0; i < this.threads.Length; ++i)
            {
                var thread = new Thread(ThreadMain);
                this.threads[i] = thread;
                this.clients[i] = this.connect();
                thread.Start(Tuple.Create(i, rng.Next()));
            }

            Console.Out.WriteLine("Waiting for connections to complete...");
            this.startBarrier.SignalAndWait();

            Console.Out.WriteLine("Test started. Waiting for completion...");
            foreach (var t in this.threads)
            {
                t.Join();
            }
            Console.Out.WriteLine("Test completed.");
        }

        protected abstract void OnRequest(ulong reqNum, KeyValueStoreClient client, Random random);

        static protected ulong TicksToMilliseconds(long ticks)
        {
            return (ulong)(ticks * 1.0 / Stopwatch.Frequency * 1000);
        }

        private void ThreadMain(object obj)
        {
            var args = (Tuple<int, int>)obj;
            int clientId = args.Item1;
            var random = new Random(args.Item2);
            var client = this.clients[clientId];
            var stopwatch = new Stopwatch();

            this.startBarrier.SignalAndWait();
            stopwatch.Start();

            ulong reqNum = 0;
            while (stopwatch.ElapsedTicks < this.durationTicks)
            {
                var t0 = stopwatch.ElapsedTicks;
                this.OnRequest(reqNum, client, random);
                var t1 = stopwatch.ElapsedTicks;
                var tMs0 = TicksToMilliseconds(t0);
                var tMs1 = TicksToMilliseconds(t1);
                lock (this.textWriter)
                {
                    this.textWriter.WriteLine("#req{0} {1} {2} {3}", reqNum, tMs0, tMs1, clientId);
                }
                ++reqNum;
            }
        }
    }
}
