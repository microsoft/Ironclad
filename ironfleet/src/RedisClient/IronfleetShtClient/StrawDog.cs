namespace IronfleetShtClient
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics;
    using System.IO;
    using System.Linq;
    using System.Text;
    using System.Threading.Tasks;

    public class StrawDog : Experiment
    {
        private readonly Vocabulary keys;
        private readonly Vocabulary values;

        public StrawDog(Func<KeyValueStoreClient> connect, int clientCount, long durationMs, int valueBytes, Random rng, TextWriter textWriter) :
            base(connect, clientCount, durationMs, textWriter)
        {
            if (0 >= valueBytes)
            {
                throw new ArgumentOutOfRangeException("valueBytes");
            }

            Console.Out.WriteLine("Generating test data...");
            // set up pools of random byte strings for experiment.
            this.keys = new Vocabulary(rng, new Dictionary<int, int> { { 8 /*bytes*/, 1000/*entries*/ } });
            this.values = new Vocabulary(rng, new Dictionary<int, int> { { valueBytes, 1000 } });
        }

        protected override void OnRequest(ulong reqNum, KeyValueStoreClient client, Random rng)
        {
            Debug.Assert(client != null, "client is expected to be non-null");
            Debug.Assert(rng != null, "random is expected to be non-null");
            Debug.Assert(this.keys != null, "key vocabulary is expected to be non-null");
            Debug.Assert(this.values != null, "value vocabulary is expected to be non-null");

            var key = this.keys.Pick(rng);
            /*if ((reqNum & 1) == 0)
            {
                var value = this.values.Pick(rng);
                client.SetValue(key, value);            
            }
            else*/
            {
                client.GetValue(key);            
            }
        }
    }
}
